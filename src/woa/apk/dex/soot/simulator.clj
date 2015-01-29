(ns woa.apk.dex.soot.simulator
  ;; internal libs
  (:require [woa.util
             :refer [print-stack-trace-if-verbose]])   
  (:use woa.apk.dex.soot.util)
  (:use woa.apk.dex.soot.sexp)
  ;; common libs
  (:require [clojure.string :as str]
            [clojure.set :as set]
            [clojure.walk :as walk]
            [clojure.zip :as zip]
            [clojure.java.io :as io]
            [clojure.pprint :refer [pprint print-table]]
            [clojure.stacktrace :refer [print-stack-trace]])
  ;; imports
  (:import (soot Unit
                 SootField
                 SootClass
                 SootMethod
                 SootMethodRef

                 Local

                 RefLikeType
                 ArrayType
                 RefType)
           
           (soot.jimple Stmt
                        StmtSwitch
                        JimpleValueSwitch)))

;;; declaration

;; public
(declare with-simulator)
(declare initialize-classes get-all-interesting-invokes)
(declare ^:dynamic *init-instances* ^:dynamic *simulator-global-state*)

;; private

(declare simulate-method simulate-basic-block)
(declare create-simulator 
         simulator-evaluate simulator-new-instance
         simulator-get-field simulator-set-field
         simulator-get-this simulator-get-param
         simulator-set-local simulator-get-local
         simulator-add-returns simulator-get-returns simulator-clear-returns
         simulator-add-explicit-invokes simulator-get-explicit-invokes simulator-clear-explicit-invokes
         simulator-add-implicit-invokes simulator-get-implicit-invokes simulator-clear-implicit-invokes
         simulator-add-component-invokes simulator-get-component-invokes simulator-clear-component-invokes)
(declare filter-implicit-cf-invoke-methods
         implicit-cf-class? implicit-cf? implicit-cf-task? implicit-cf-component? 
         get-transitive-implicit-cf-super-class-and-interface get-implicit-cf-root-class-names)
(declare implicit-cf-marker implicit-cf-marker-task implicit-cf-marker-component)
(declare safe-invokes)

;;; implementation

;; value resolver protocol
(defprotocol SimulatorValueResolver
  (simulator-resolve-value [obj simulator]))

;; the default case
(extend-type nil
  SimulatorValueResolver
  (simulator-resolve-value [object simulator]
    nil))

(extend-type Object
  SimulatorValueResolver
  (simulator-resolve-value [object simulator]
    object))

(extend-type soot.Local
  SimulatorValueResolver
  (simulator-resolve-value [local simulator]
    (let [value (simulator-get-local simulator local)]
      (if (= value :nil)
        (make-local-sexp local)
        (simulator-resolve-value value simulator)))))

(extend-type soot.SootField
  SimulatorValueResolver
  (simulator-resolve-value [field simulator]
    (let [instance (simulator-get-this simulator)
          value (simulator-get-field instance field)]
      (if (= value :nil)
        (make-field-sexp instance field)
        (simulator-resolve-value value simulator)))))

(extend-type soot.SootFieldRef
  SimulatorValueResolver
  (simulator-resolve-value [field simulator]
    (let [instance (simulator-get-this simulator)
          value (simulator-get-field instance field)]
      (if (= value :nil)
        (make-field-sexp instance field)
        (simulator-resolve-value value simulator)))))

(extend-type soot.jimple.InstanceFieldRef
  SimulatorValueResolver
  (simulator-resolve-value [field simulator]
    (let [instance (simulator-resolve-value (.. field getBase) simulator)
          field (.. field getFieldRef)
          value (simulator-get-field instance field)]
      (if (= value :nil)
        (make-field-sexp instance field)
        (simulator-resolve-value value simulator)))))

(extend-type soot.jimple.FieldRef
  SimulatorValueResolver
  (simulator-resolve-value [field simulator]
    (let [instance (simulator-get-this simulator)
          field (.. field getFieldRef)
          value (simulator-get-field instance field)]
      (if (= value :nil)
        (make-field-sexp instance field)
        (simulator-resolve-value value simulator)))))

(extend-type soot.jimple.MethodHandle
  SimulatorValueResolver
  (simulator-resolve-value [method-handle simulator]
    (let [value (make-method-sexp (.. method-handle methodRef))]
      (simulator-resolve-value value simulator))))

(extend-type soot.jimple.NullConstant
  SimulatorValueResolver
  (simulator-resolve-value [_ simulator]
    nil))

(extend-type soot.jimple.ClassConstant
  SimulatorValueResolver
  (simulator-resolve-value [const simulator]
    (let [value (make-class-sexp (.. const getType getSootClass))]
      (simulator-resolve-value value simulator))))

(extend-type soot.jimple.Constant
  SimulatorValueResolver
  (simulator-resolve-value [const simulator]
    (.. const value)))

(extend-type woa.apk.dex.soot.sexp.InstanceSexp
  SimulatorValueResolver
  (simulator-resolve-value [this simulator]
    (:instance this)))

;; simulator assignment protocol

(defprotocol SimulatorAssignment
  "simulator should be an atom to have persistent effect"
  (simulator-assign [target value simulator]))

(extend-type nil
  SimulatorAssignment
  (simulator-assign [local value simulator]
    nil))

(extend-type soot.Local
  SimulatorAssignment
  (simulator-assign [local value simulator]
    (swap! simulator simulator-set-local
           local value)))

(extend-type soot.SootField
  SimulatorAssignment
  (simulator-assign [field value simulator]
    (simulator-set-field (simulator-get-this @simulator)
                         field value)))

(extend-type soot.SootFieldRef
  SimulatorAssignment
  (simulator-assign [field value simulator]
    (simulator-set-field (simulator-get-this @simulator)
                         field value)))

(extend-type soot.jimple.FieldRef
  SimulatorAssignment
  (simulator-assign [field value simulator]
    (simulator-assign (.. field getFieldRef) value simulator)))

(extend-type soot.jimple.ArrayRef
  SimulatorAssignment
  (simulator-assign [field value simulator]
    (let [base (.. field getBase)
          base-value (-> base (simulator-resolve-value @simulator))
          index-value (-> (.. field getIndex)
                          (simulator-resolve-value @simulator))]
      (simulator-assign base
                        (assoc base-value index-value value)
                        simulator))))

;;
;; get method interesting invokes and helpers
;; 

(def ^:dynamic *init-instances*
  "initial instance of classes with circumscription"
  nil)

(def ^:dynamic *simulator-global-state*
  "initialized in initialize-classes to avoid unintentional retation"
  nil)

(defmacro with-simulator
  [& body]
  `(binding [*init-instances* (atom nil)
             *simulator-global-state* (atom nil)]
     ~@body))

(defn initialize-classes
  "initialize class by invoking <clinit>"
  [{:keys [classes circumscription]
    :or {circumscription :all}
    :as initialize-params}
   {:keys [verbose]
    :as options}]
  (reset! *simulator-global-state*
          {:fields {:static {}
                    :instance {}}})
  (let [;; soot.SootMethod cannot be reliably compared for value (as in a set)
        circumscription (if (= circumscription :all)
                          circumscription
                          (try
                            (->> circumscription
                                 (map #(.. % getSignature))
                                 set)
                            (catch Exception e
                              (set circumscription))))]
    (doseq [^SootClass class classes]
      (swap! *init-instances* assoc-in [class]
             (simulator-new-instance class))
      (doseq [^SootMethod clinit (.. (soot.EntryPoints/v) (clinitsOf class))]
        (try
          (simulate-method {:method clinit
                            :this nil
                            :params nil}
                           (assoc-in options [:circumscription]
                                     circumscription))
          (catch Exception e
            (print-stack-trace-if-verbose e verbose 3)))))))

(defn get-all-interesting-invokes
  "get both explicit and implicit interesting invokes"
  [^SootMethod root-method
   interesting-method?
   circumscription
   {:keys [verbose]
    :as options}]
  (let [all-explicit-invokes (atom #{})
        all-implicit-invokes (atom #{})
        all-component-invokes (atom #{})
        ;; soot.SootMethod cannot be reliably compared for value (as in a set)
        circumscription (if (= circumscription :all)
                          circumscription
                          (try
                            (->> circumscription
                                 (map #(.. % getSignature))
                                 set)
                            (catch Exception e
                              (set circumscription))))]
    (try
      (let [{:keys [explicit-invokes
                    implicit-invokes
                    component-invokes]}
            ;; full simulation
            (simulate-method {:method
                              root-method
                              :this
                              ;; use initial instance if available
                              (let [root-method-class (-> root-method get-soot-class)
                                    instance (get-in @*init-instances*
                                                     [root-method-class])]
                                (if instance
                                  instance
                                  (simulator-new-instance root-method-class)))
                              :params
                              (->> (.. root-method getParameterTypes)
                                   (map #(make-external-sexp :instance
                                                             {:type %})))
                              :interesting-method?
                              interesting-method?}
                             (assoc-in options [:circumscription]
                                       circumscription))]
        
        ;; interesting invokes can be explicit or implicit
        (swap! all-explicit-invokes into
               explicit-invokes)
        (swap! all-implicit-invokes into
               implicit-invokes)
        (swap! all-component-invokes into
               component-invokes))
      (catch Exception e
        (print-stack-trace-if-verbose e verbose 3)))
    ;; return result
    {:explicit-invokes @all-explicit-invokes
     :implicit-invokes @all-implicit-invokes
     :component-invokes @all-component-invokes}))

(defn- simulate-method
  "simulate method"
  [{:keys [method this params interesting-method?]
    :or {interesting-method? (constantly true)}
    :as simulation-params}
   {:keys [circumscription
           soot-basic-block-simulation-budget
           soot-method-simulation-depth-budget]
    :or {circumscription :all}
    :as options}]
  
  ;; method could be soot.SootMethodRef, so may need .resolve
  (let [method (try
                 (.. method resolve)
                 (catch Exception e
                   method))]
    (cond
      (not (instance? soot.SootMethod method))
      {:returns #{(make-external-sexp :invoke
                                      {:method method
                                       :this this
                                       :params params})}
       :explicit-invokes #{}
       :implicit-invokes #{}
       :component-invokes #{}}      
      
      ;; only simulate method within circumscription
      (and (not= circumscription :all)
           (not (contains? circumscription
                           (.. method getSignature))))
      (do
        {:returns #{(make-external-sexp :invoke
                                        {:method method
                                         :this this
                                         :params params})}
         :explicit-invokes #{}
         :implicit-invokes #{}
         :component-invokes #{}})
      
      (< soot-method-simulation-depth-budget 0)
      (do
        {:returns #{(make-error-sexp :no-budget
                                     {:method method
                                      :this this
                                      :params params})}
         :explicit-invokes #{}
         :implicit-invokes #{}
         :component-invokes #{}})

      ;; no method body, cannot proceed
      (not (.. method hasActiveBody))
      (do
        {:returns #{(make-error-sexp :no-method-body
                                     {:method method
                                      :this this
                                      :params params})}
         :explicit-invokes #{}
         :implicit-invokes #{}
         :component-invokes #{}})

      :otherwise
      (let [all-returns (atom #{})
            all-explicit-invokes (atom #{})
            all-implicit-invokes (atom #{})
            all-component-invokes (atom #{})
            
            body (.. method getActiveBody)

            stmt-info
            (let [stmts (->> (.. body getUnits snapshotIterator) iterator-seq vec)
                  stmt-2-index (->> stmts
                                    (map-indexed #(vector %2 %1))
                                    (into {}))]
              {:stmts stmts
               :stmt-2-index stmt-2-index})

            bb-budget (atom soot-basic-block-simulation-budget)]
        (process-worklist
         ;; the initial worklist
         #{{:simulator (create-simulator this params)
            :start-stmt (first (:stmts stmt-info))}}
         ;; the process
         (fn [worklist]
           (when (and @bb-budget
                      (> @bb-budget 0))
             ;; width-first search to prevent malicious code exhaust bb-budget
             (->> worklist
                  (mapcat (fn [{:keys [simulator start-stmt]}]
                            (let [{:keys [simulator next-start-stmts]}
                                  (simulate-basic-block {:simulator simulator
                                                         :stmt-info stmt-info
                                                         :start-stmt start-stmt
                                                         :method method
                                                         :interesting-method?
                                                         interesting-method?}
                                                        options)]

                              (swap! bb-budget dec)
                              (swap! all-returns into
                                     (-> simulator
                                         simulator-get-returns))
                              (swap! all-explicit-invokes into
                                     (-> simulator
                                         simulator-get-explicit-invokes))
                              (swap! all-implicit-invokes into
                                     (-> simulator
                                         simulator-get-implicit-invokes))
                              (swap! all-component-invokes into
                                     (-> simulator
                                         simulator-get-component-invokes))
                              ;; add the following to worklist
                              (when (and @bb-budget
                                         (> @bb-budget 0))
                                (for [start-stmt (set next-start-stmts)]
                                  ;; control flow sensitive!
                                  {:simulator (-> simulator
                                                  simulator-clear-returns
                                                  simulator-clear-explicit-invokes
                                                  simulator-clear-implicit-invokes
                                                  simulator-clear-component-invokes)
                                   :start-stmt start-stmt})))))))))
        {:returns @all-returns
         :explicit-invokes @all-explicit-invokes
         :implicit-invokes @all-implicit-invokes
         :component-invokes @all-component-invokes}))))

(defn- simulate-basic-block
  "simulate a basic block"
  [{:keys [simulator stmt-info start-stmt method interesting-method?]
    :as simulation-params}
   {:keys [soot-method-simulation-depth-budget
           verbose]
    :as options}]
  (let [simulator (atom simulator)

        ;; split at first branch or return
        [basic-block residue]
        (split-with #(let [^Stmt stmt %]
                       (and (.. stmt fallsThrough)
                            (not (.. stmt branches))))
                    (subvec (:stmts stmt-info)
                            (get (:stmt-2-index stmt-info)
                                 start-stmt)))]
    ;; simulate statements in the basic block
    (doseq [^Stmt stmt basic-block]
      (.. stmt
          (apply (proxy [StmtSwitch] []
                   (caseAssignStmt [stmt]
                     (let [target (.. stmt getLeftOp)
                           value (-> (.. stmt getRightOp)
                                     (simulator-evaluate
                                      {:simulator simulator
                                       :interesting-method?
                                       interesting-method?}
                                      options))]
                       (simulator-assign target value simulator)))
                   (caseBreakpointStmt [stmt])
                   (caseEnterMonitorStmt [stmt])
                   (caseExitMonitorStmt [stmt])
                   (caseGotoStmt [stmt])
                   (caseIdentityStmt [stmt]
                     (try
                       (let [target (.. stmt getLeftOp)
                             value(-> (.. stmt getRightOp)
                                      (simulator-evaluate
                                       {:simulator simulator
                                        :interesting-method?
                                        interesting-method?}
                                       options))]
                         (simulator-assign target value simulator))
                       (catch Exception e
                         (print-stack-trace-if-verbose e verbose 4))))
                   (caseIfStmt [stmt])
                   (caseInvokeStmt [stmt]
                     (try
                       (-> (.. stmt getInvokeExpr)
                           (simulator-evaluate {:simulator simulator
                                                :interesting-method?
                                                interesting-method?}
                                               options))
                       (catch Exception e
                         (print-stack-trace-if-verbose e verbose 4))))
                   (caseLookupSwitchStmt [stmt])
                   (caseNopStmt [stmt])
                   (caseRetStmt [stmt])
                   (caseReturnStmt [stmt])
                   (caseReturnVoidStmt [stmt])
                   (caseTableSwitchStmt [stmt])
                   (caseThrowStmt [stmt])
                   (defaultCase [stmt]))))
      (when (and verbose (> verbose 4))
        (println "------")
        (println stmt)
        (pprint (:locals @simulator))))
    (let [return (atom {:simulator nil ; to be filled at the end
                        :next-start-stmts #{}})
          ;; the first stmt of residue, if existed, is a brancher
          stmt (first residue)]
      (when stmt
        (.. stmt
            (apply (proxy [StmtSwitch] []
                     (caseAssignStmt [stmt])
                     (caseBreakpointStmt [stmt])
                     (caseEnterMonitorStmt [stmt])
                     (caseExitMonitorStmt [stmt])
                     (caseGotoStmt [^soot.jimple.internal.JGotoStmt stmt]
                       (swap! return update-in [:next-start-stmts]
                              conj (.. stmt getTarget)))                     
                     (caseIdentityStmt [stmt])
                     (caseIfStmt [^soot.jimple.internal.JIfStmt stmt]
                       (let [condition (.. stmt getCondition)
                             value (-> condition
                                       (simulator-evaluate {:simulator simulator
                                                            :interesting-method?
                                                            interesting-method?}
                                                           options))                             
                             target-stmt (.. stmt getTarget)
                             next-stmt (second residue)]
                         (if-not (extends? Sexp (class value))
                           (if value
                             ;; if value is true, take target-stmt
                             (when target-stmt
                               (swap! return update-in [:next-start-stmts]
                                      conj target-stmt))
                             ;; if value is false, take next-stmt
                             (when next-stmt
                               (swap! return update-in [:next-start-stmts]
                                      conj next-stmt)))
                           ;; otherwise, take both stmts
                           (doseq [stmt [next-stmt target-stmt]
                                   :when stmt]
                             (swap! return update-in [:next-start-stmts]
                                    conj stmt)))))                     
                     (caseInvokeStmt [stmt])
                     (caseLookupSwitchStmt [stmt])
                     (caseNopStmt [stmt])
                     (caseRetStmt [stmt])
                     (caseReturnStmt [stmt]
                       (doto simulator
                         (swap! simulator-add-returns
                                [(-> (.. stmt getOp)
                                     (simulator-evaluate {:simulator simulator
                                                          :interesting-method?
                                                          interesting-method?}
                                                         options))])))
                     (caseReturnVoidStmt [stmt]
                       ;; nothing to do
                       )
                     (caseTableSwitchStmt [stmt])
                     (caseThrowStmt [stmt])
                     (defaultCase [stmt])))))
      (swap! return assoc-in [:simulator]
             @simulator)
      @return)))

;;
;; frame simulator manipulators
;; 

(defrecord ^:private Simulator
  [;; for a method frame
   this params locals returns
   ;; during simulation
   explicit-invokes implicit-invokes component-invokes])

(defn- create-simulator
  [this params]
  (map->Simulator {:this this
                   :params (vec params)
                   :locals {}
                   :returns #{}
                   :explicit-invokes #{}
                   :implicit-invokes #{}
                   :component-invokes #{}}))

(defn- simulator-new-instance
  [& [class]]
  (let [instance (gensym (str "instance"
                              (when-let [class-name (get-soot-class-name class)]
                                (str "-" class-name))))]
    (make-instance-sexp class instance)))



(defn- simulator-evaluate
  "evaluate expr in simulator (simulator should be an Clojure atom to allow updates)"
  [expr
   {:keys [simulator interesting-method?]
    :as simulation-params}
   {:keys [soot-method-simulation-depth-budget
           soot-result-include-invoke-arguments
           soot-no-implicit-cf
           soot-dump-all-invokes
           verbose]
    :as options}]
  (let [result (atom nil)

        ;; binary operation
        binary-operator-expr
        (fn [expr operator]
          (let [op1 (-> (.. expr getOp1) (simulator-resolve-value @simulator))
                op2 (-> (.. expr getOp2) (simulator-resolve-value @simulator))
                default-return (make-binary-operator-sexp operator [op1 op2])]
            (try
              (operator op1 op2)
              (catch Exception e
                (print-stack-trace-if-verbose e verbose 4)
                default-return))))
        
        ;; unary operation
        unary-operator-expr
        (fn [expr operator]
          (let [op (-> (.. expr getOp) (simulator-resolve-value @simulator))
                default-return (make-unary-operator-sexp operator [op])]
            (try
              (operator op)
              (catch Exception e
                (print-stack-trace-if-verbose e verbose 4)
                default-return)))) 
        
        ;; invoke operation
        invoke-expr
        (fn [invoke-type ^SootMethodRef method base args]
          (let [base-value (simulator-resolve-value base @simulator)
                args (->> args
                          (map #(simulator-resolve-value % @simulator))
                          vec) 
                default-return (make-invoke-sexp invoke-type
                                                 method
                                                 base-value
                                                 args)
                method-class (-> method get-soot-class)
                class-name (-> method get-soot-class-name)
                method-name (-> method get-soot-name)]
            
            (try
              
              ;; only add interesting methods
              (when (or soot-dump-all-invokes
                        (interesting-method? method))
                (doto simulator
                  (swap! simulator-add-explicit-invokes
                         (if soot-result-include-invoke-arguments
                           [{:method method
                             :args args}]
                           [method]))))

              (let [invoke-method (fn [method this params & [implicit?]]
                                    (when (or soot-dump-all-invokes
                                              (interesting-method? method))
                                      (doto simulator
                                        (swap! (if implicit?
                                                 simulator-add-implicit-invokes
                                                 simulator-add-explicit-invokes)
                                               (if soot-result-include-invoke-arguments
                                                 [{:method method
                                                   :args args}]
                                                 [method]))))
                                    
                                    (let [{:keys [returns
                                                  explicit-invokes
                                                  implicit-invokes
                                                  component-invokes]}
                                          (simulate-method {:method method
                                                            :this this
                                                            :params params
                                                            :interesting-method?
                                                            interesting-method?}
                                                           (update-in options
                                                                      [:soot-method-simulation-depth-budget]
                                                                      dec))]
                                      (do
                                        (doto simulator
                                          ;; implicit is contagious
                                          (swap! (if implicit?
                                                   simulator-add-implicit-invokes
                                                   simulator-add-explicit-invokes)
                                                 explicit-invokes)
                                          (swap! simulator-add-implicit-invokes
                                                 implicit-invokes)
                                          (swap! simulator-add-component-invokes
                                                 component-invokes))
                                        ;; if the result is unique, extract it
                                        (if (== 1 (count returns))
                                          (first returns)
                                          returns))))]
                (cond
                  
                  ;; safe invokes
                  (let [t (get safe-invokes class-name)]
                    (or (= t :all)
                        (contains? t method-name)))
                  (try
                    (cond
                      
                      ;; special invokes: <init>
                      (= invoke-type :special-invoke)
                      (let [args (into-array args)]
                        (simulator-assign base
                                          (.. (Class/forName class-name)
                                              (getConstructor args)
                                              (newInstance args))
                                          simulator))

                      ;; other invokes
                      (not (extends? Sexp (class base-value)))
                      (let [args (into-array args)]
                        (.. (Class/forName class-name)
                            (getMethod method-name args)
                            (invoke base-value args))))
                    (catch Exception e
                      (invoke-method method base-value args)))

                  ;; implicit cf: task
                  (and (not soot-no-implicit-cf)
                       (implicit-cf-task? method))
                  (try
                    (let [root-class-name (->> method
                                               get-implicit-cf-root-class-names
                                               first)
                          x [root-class-name method-name]]
                      (cond
                        (#{["java.lang.Thread" "start"]
                           ["java.lang.Runnable" "run"]}
                         x)
                        (when-let [implicit-target (.. method-class
                                                       (getMethodByNameUnsafe "run"))]
                          (invoke-method implicit-target base-value [] true))

                        (#{["java.util.concurrent.Callable" "call"]}
                         x)
                        (when-let [implicit-target (.. method-class
                                                       (getMethodByNameUnsafe "call"))]
                          (invoke-method implicit-target base-value [] true))

                        (#{["java.util.concurrent.Executor" "execute"]
                           ["java.util.concurrent.ExecutorService" "execute"]}
                         x)
                        (let [target-obj (first args)]
                          (when-let [implicit-target
                                     (.. (-> target-obj get-soot-class)
                                         (getMethodByNameUnsafe "run"))]
                            (invoke-method implicit-target target-obj [] true)))

                        (#{["java.util.concurrent.ExecutorService" "submit"]}
                         x)
                        (let [target-obj (first args)]
                          (when-let [implicit-target
                                     (.. (-> target-obj get-soot-class)
                                         (getMethodByNameUnsafe "run"))]
                            (invoke-method implicit-target target-obj [] true))
                          (when-let [implicit-target
                                     (.. (-> target-obj get-soot-class)
                                         (getMethodByNameUnsafe "call"))]
                            (invoke-method implicit-target target-obj [] true)))

                        (#{["android.os.Handler" "post"]
                           ["android.os.Handler" "postAtFrontOfQueue"]
                           ["android.os.Handler" "postAtTime"]
                           ["android.os.Handler" "postDelayed"]}
                         x)
                        (let [target-obj (first args)]
                          (when-let [implicit-target
                                     (.. (-> target-obj get-soot-class)
                                         (getMethodByNameUnsafe "run"))]
                            (invoke-method implicit-target target-obj [] true)))

                        (#{["java.lang.Class" "forName"]}
                         x)
                        (let [target-obj (first args)]
                          (try
                            (-> target-obj get-soot-class)
                            (catch Exception e
                              (make-class-sexp target-obj))))

                        (#{["java.lang.Class" "getMethod"]}
                         x)
                        (let [target-obj (first args)]
                          (try
                            (.. (-> base-value get-soot-class)
                                (getMethodByNameUnsafe (str target-obj)))
                            (catch Exception e
                              (make-method-sexp base-value target-obj))))

                        (#{["java.lang.reflect.Method" "invoke"]}
                         x)
                        (try
                          (when (and verbose (> verbose 3))
                            (println "java.lang.reflect.Method.invoke:" base-value args))
                          (if (.. base-value isStatic)
                            (invoke-method base-value nil args true)
                            (invoke-method base-value (first args) (vec (rest args)) true))
                          (catch Exception e
                            (make-invoke-sexp :reflect base-value (first args) (vec (rest args)))))
                        
                        (#{["java.lang.Class" "getField"]}
                         x)
                        (let [target-obj (first args)]
                          (try
                            (.. (-> base-value get-soot-class)
                                (getFieldByNameUnsafe (str target-obj)))
                            (catch Exception e
                              (make-field-sexp base-value target-obj))))

                        (and (= "java.lang.reflect.Field" root-class-name)
                             (#{"get" "getBoolean" "getByte" "getChar"
                                "getDouble" "getFloat" "getInt" "getLong" "getShort"}
                              method-name))
                        (try
                          (let [field (simulator-get-local @simulator base)
                                value (simulator-get-field (simulator-get-this @simulator)
                                                           field)]
                            (when (and verbose (> verbose 3))
                              (println (format "java.lang.reflect.Field.%1$s: %2$s=%3$s"
                                               method-name field value)))
                            value)
                          (catch Exception e
                            (make-field-sexp (simulator-get-this @simulator) base-value)))

                        (and (= "java.lang.reflect.Field" root-class-name)
                             (#{"equals"}) method-name)
                        (try
                          (let [field (simulator-get-local @simulator base)
                                value (simulator-get-field (simulator-get-this @simulator)
                                                           field)]
                            (= value (first args)))
                          (catch Exception e
                            (make-field-sexp (simulator-get-this @simulator)
                                             base-value)))

                        (and (= "java.lang.reflect.Field" root-class-name)
                             (#{"set" "setBoolean" "setByte" "setChar"
                                "setDouble" "setFloat" "setInt" "setLong" "setShort"}
                              method-name))
                        (try
                          (let [field (simulator-get-local @simulator base)
                                value (first args)]
                            (simulator-set-field (simulator-get-this @simulator)
                                                 field value)                            
                            (when (and verbose (> verbose 3))
                              (println (format "java.lang.reflect.Field.%1$s: %2$s=%3$s"
                                               method-name
                                               field
                                               value)))
                            value)
                          (catch Exception e
                            (make-field-sexp (simulator-get-this @simulator) base-value)))

                        :default (invoke-method method base-value args true)))
                    (catch Exception e
                       (invoke-method method base-value args true)))

                  ;; implicit cf: component
                  (and (not soot-no-implicit-cf)
                       (implicit-cf-component? method))
                  (try
                    (let [root-class-name (->> method
                                               get-implicit-cf-root-class-names
                                               first)
                          x [root-class-name method-name]]
                      (cond


;;                   (#{["android.content.Context" "startActivity"]
;;                      ["android.content.Context" "startActivities"]}
;;                    x)
;;                   (update-result :category :component
;;                                  :type "android.app.Activity"
;;                                  :instance (with-out-str (pr (first args))))

;;                   (#{["android.content.Context" "startService"]
;;                      ["android.content.Context" "stopService"]
;;                      ["android.content.Context" "bindService"]
;;                      ["android.content.Context" "unbindService"]}
;;                    x)
;;                   (update-result :category :component
;;                                  :type "android.app.Service"
;;                                  :instance (with-out-str (pr (first args))))

;;                   (#{["android.content.Context" "sendBroadcast"]
;;                      ["android.content.Context" "sendBrocastAsUser"]
;;                      ["android.content.Context" "sendOrderedBroadcast"]
;;                      ["android.content.Context" "sendOrderedBroadcastAsUser"]
;;                      ["android.content.Context" "sendStickyBroadcast"]
;;                      ["android.content.Context" "sendStickyBroadcastAsUser"]}
;;                    x)
;;                   (update-result :category :component
;;                                  :type "android.content.BroadcastReceiver"
;;                                  :instance (with-out-str (pr (first args))))

;;                   (#{["android.content.Context" "registerComponentCallbacks"]}
;;                    x)
;;                   (update-result :category :component
;;                                  :type "android.content.ComponentCallbacks"
;;                                  :instance (with-out-str (pr (first args))))

;;                   (#{["android.content.Context" "registerReceiver"]}
;;                    x)
;;                   (update-result :category :component
;;                                  :type "android.content.BroadcastReceiver"
;;                                  :instance (with-out-str (pr args))))))))

                        
                        :default (invoke-method method base-value args true)))
                    (catch Exception e
                      (invoke-method method base-value args true)))

                  :default
                  (invoke-method method base-value args)))
              
              (catch Exception e
                (print-stack-trace-if-verbose e verbose 4)
                default-return))))]
    (try
      (.. expr
          (apply
           (proxy [JimpleValueSwitch] []
             ;; case local
             (caseLocal [local]
               (reset! result
                       (simulator-resolve-value local @simulator)))
             ;; ConstantSwitch
             (caseClassConstant [const]
               (reset! result
                       (simulator-resolve-value const @simulator)))
             (caseDoubleConstant [const]
               (reset! result
                       (simulator-resolve-value const @simulator)))
             (caseFloatConstant [const]
               (reset! result
                       (simulator-resolve-value const @simulator)))
             (caseIntConstant [const]
               (reset! result
                       (simulator-resolve-value const @simulator)))
             (caseLongConstant [const]
               (reset! result
                       (simulator-resolve-value const @simulator)))
             (caseMethodHandle [const]
               (reset! result
                       (simulator-resolve-value const @simulator)))
             (caseNullConstant [const]
               (reset! result
                       (simulator-resolve-value const @simulator)))
             (caseStringConstant [const]
               (reset! result
                       (simulator-resolve-value const @simulator)))
             ;; ExprSwitch
             (caseAddExpr [expr]
               (reset! result
                       (binary-operator-expr expr +)))
             (caseAndExpr [expr]
               (reset! result
                       (binary-operator-expr expr bit-and)))
             (caseCastExpr [expr]
               ;; no effect on result
               )
             (caseCmpExpr [expr]
               (reset! result
                       (binary-operator-expr expr compare)))
             (caseCmpgExpr [expr]
               ;; JVM-specific artifacts; N/A on Dalvik
               (reset! result
                       (binary-operator-expr expr compare)))
             (caseCmplExpr [expr]
               ;; JVM-specific artifacts; N/A on Dalvik
               (reset! result
                       (binary-operator-expr expr compare)))
             (caseDivExpr [expr]
               (reset! result
                       (binary-operator-expr expr /)))
             (caseDynamicInvokeExpr [expr]
               ;; JVM8 specific; N/A on Dalvik
               (reset! result
                       (invoke-expr :dynamic-invoke
                                    (.. expr getBootstrapMethodRef)
                                    nil
                                    (.. expr getBootstrapArgs))))
             (caseEqExpr [expr]
               (reset! result
                       ;; only non-sexp can be meaningfully compared
                       (binary-operator-expr
                        expr
                        (fn [op1 op2]
                          (if (and (not (extends? Sexp (class op1)))
                                   (not (extends? Sexp (class op2))))
                            (== op1 op2)
                            (make-binary-operator-sexp == [op1 op2]))))))
             (caseGeExpr [expr]
               (reset! result
                       (binary-operator-expr expr >=)))
             (caseGtExpr [expr]
               (reset! result
                       (binary-operator-expr expr >)))
             (caseInstanceOfExpr [expr]
               (reset! result
                       (let [check-type (-> (.. expr getCheckType) (simulator-resolve-value @simulator))
                             op (-> (.. expr getOp) (simulator-resolve-value @simulator))
                             default-return (make-instance-of-sexp check-type op)]
                         (try
                           (let [check-type-class (-> check-type get-soot-class)
                                 check-type-name (-> check-type get-soot-class-name)]
                             (cond
                               (instance? woa.apk.dex.soot.sexp.InvokeSexp op)
                               (let [method (:method op)
                                     return-type (cond
                                                   (instance? soot.SootMethodRef method)
                                                   (.. method returnType)
                                                   (instance? soot.SootMethod method)
                                                   (.. method getReturnType))
                                     type-class (-> return-type get-soot-class)]
                                 (if (transitive-ancestor? check-type-class
                                                           type-class)
                                   ;; only positive answer is certain
                                   1
                                   default-return))

                               :default default-return))
                           (catch Exception e
                             (print-stack-trace-if-verbose e verbose 4)
                             default-return)))))
             (caseInterfaceInvokeExpr [expr]
               (reset! result
                       (invoke-expr :interface-invoke
                                    (.. expr getMethodRef)
                                    (.. expr getBase)
                                    (.. expr getArgs))))
             (caseLeExpr [expr]
               (reset! result
                       (binary-operator-expr expr <=)))
             (caseLengthExpr [expr]
               (reset! result
                       (unary-operator-expr expr count)))
             (caseLtExpr [expr]
               (reset! result
                       (binary-operator-expr expr <)))
             (caseMulExpr [expr]
               (reset! result
                       (binary-operator-expr expr *)))
             (caseNeExpr [expr]
               (reset! result
                       ;; only non-sexp can be meaningfully compared                       
                       (binary-operator-expr
                        expr
                        (fn [op1 op2]
                          (if (and (not (extends? Sexp (class op1)))
                                   (not (extends? Sexp (class op2))))
                            (not= op1 op2)
                            (make-binary-operator-sexp not= [op1 op2]))))))
             (caseNegExpr [expr]
               (reset! result
                       (unary-operator-expr expr -)))
             (caseNewArrayExpr [expr]
               (reset! result
                       (let [base-type (-> (.. expr getBaseType)
                                           (simulator-resolve-value @simulator))
                             size (-> (.. expr getSize)
                                      (simulator-resolve-value @simulator))
                             default-return (make-new-array-sexp base-type size)]
                         (try
                           (->> (repeat size nil)
                                vec)
                           (catch Exception e
                             (print-stack-trace-if-verbose e verbose 4)
                             default-return)))))
             (caseNewExpr [expr]
               ;; will be evaluated in caseSpecialInvokeExpr where the arguments are ready
               )
             (caseNewMultiArrayExpr [expr]
               (reset! result
                       (let [base-type (-> (.. expr getBaseType)
                                           (simulator-resolve-value @simulator))
                             sizes (->> (.. expr getSize)
                                        (map #(simulator-resolve-value % @simulator))
                                        vec)
                             default-return (make-new-multi-array-sexp base-type sizes)]
                         (try
                           (->> (repeat (reduce * sizes) nil)
                                vec)
                           (catch Exception e
                             (print-stack-trace-if-verbose e verbose 4)
                             default-return)))))
             (caseOrExpr [expr]
               (reset! result
                       (binary-operator-expr expr bit-or)))
             (caseRemExpr [expr]
               (reset! result
                       (binary-operator-expr expr rem)))
             (caseShlExpr [expr]
               (reset! result
                       (binary-operator-expr expr not=)))
             (caseShrExpr [expr]
               (reset! result
                       (binary-operator-expr expr bit-shift-right)))
             (caseSpecialInvokeExpr [expr]
               (reset! result
                       (invoke-expr :special-invoke
                                    (.. expr getMethodRef)
                                    (.. expr getBase)
                                    (.. expr getArgs))))
             (caseStaticInvokeExpr [expr]
               (reset! result
                       (invoke-expr :static-invoke
                                    (.. expr getMethodRef)
                                    nil
                                    (.. expr getArgs))))
             (caseSubExpr [expr]
               (reset! result
                       (binary-operator-expr expr -)))
             (caseUshrExpr [expr]
               (reset! result
                       (binary-operator-expr expr unsigned-bit-shift-right)))
             (caseVirtualInvokeExpr [expr]
               (reset! result
                       (invoke-expr :virtual-invoke
                                    (.. expr getMethodRef)
                                    (.. expr getBase)
                                    (.. expr getArgs))))
             (caseXorExpr [expr]
               (reset! result
                       (binary-operator-expr expr bit-xor)))
             ;; RefSwitch
             (caseArrayRef [ref]
               (reset! result
                       (let [base (-> (.. ref getBase) (simulator-resolve-value @simulator))
                             index (-> (.. ref getIndex) (simulator-resolve-value @simulator))
                             default-return (make-array-ref-sexp base index)]
                         (try
                           (get base index)
                           (catch Exception e
                             (print-stack-trace-if-verbose e verbose 4)
                             default-return)))))
             (caseCaughtExceptionRef [ref]
               ;; irrelevant
               )
             (caseInstanceFieldRef [ref]
               (reset! result
                       (simulator-resolve-value ref @simulator)))
             (caseParameterRef [ref]
               (reset! result
                       (simulator-get-param @simulator (.. ref getIndex))))
             (caseStaticFieldRef [ref]
               (reset! result
                       (simulator-resolve-value ref @simulator)))
             (caseThisRef [ref]
               (reset! result
                       (simulator-get-this @simulator)))  
             ;; default case
             (defaultCase [expr]))))
      (catch Exception e
        (print-stack-trace-if-verbose e verbose 3)))
    @result))

;; :nil signify N/A
(defn- simulator-get-field
  [instance field]
  (let [class-name (-> field get-soot-class-name)
        field-name (-> field get-soot-name)
        field-id [class-name field-name]]
    (if (.. field isStatic)
      (get-in @*simulator-global-state* [:fields :static field-id] :nil)
      (get-in @*simulator-global-state* [:fields :instance instance field-id] :nil))))

(defn- simulator-set-field
  [instance field value]
  (let [class-name (-> field get-soot-class-name)
        field-name (-> field get-soot-name)
        field-id [class-name field-name]]
    (if (.. field isStatic)
      (swap! *simulator-global-state* assoc-in [:fields :static field-id] value)
      (swap! *simulator-global-state* assoc-in [:fields :instance instance field-id] value))))

;; :nil signify N/A
(defn- simulator-get-this
  [simulator]
  (get-in simulator [:this] :nil))

;; :nil signify N/A
(defn- simulator-get-param
  [simulator param]
  (get-in simulator [:params param] :nil))

(defn- simulator-set-local
  [simulator local val]
  (assoc-in simulator [:locals local]
            val))

;; :nil signify N/A
(defn- simulator-get-local
  [simulator local]
  (get-in simulator [:locals local] :nil))

(defn- simulator-add-returns
  [simulator invokes]
  (update-in simulator [:returns] into
             invokes))

(defn- simulator-get-returns
  [simulator]
  (get-in simulator [:returns]))

(defn- simulator-clear-returns
  [simulator]
  (assoc-in simulator [:returns] #{}))

(defn- simulator-add-explicit-invokes
  [simulator invokes]
  (update-in simulator [:explicit-invokes] into
             invokes))

(defn- simulator-get-explicit-invokes
  [simulator]
  (get-in simulator [:explicit-invokes]))

(defn- simulator-clear-explicit-invokes
  [simulator]
  (assoc-in simulator [:explicit-invokes] #{}))

(defn- simulator-add-implicit-invokes
  [simulator invokes]
  (update-in simulator [:implicit-invokes] into
             invokes))

(defn- simulator-get-implicit-invokes
  [simulator]
  (get-in simulator [:implicit-invokes]))

(defn- simulator-clear-implicit-invokes
  [simulator]
  (assoc-in simulator [:implicit-invokes] #{}))

(defn- simulator-add-component-invokes
  [simulator invokes]
  (update-in simulator [:component-invokes] into
             invokes))

(defn- simulator-get-component-invokes
  [simulator]
  (get-in simulator [:component-invokes]))

(defn- simulator-clear-component-invokes
  [simulator]
  (assoc-in simulator [:component-invokes] #{}))

;;
;; implicit control flow helpers
;; 

(defn filter-implicit-cf-invoke-methods
  "filter methods that contain implicit control flow invokes"
  [methods]
  (->> methods
       (filter
        (fn [^SootMethod method]
          (->> [method]
               mapcat-invoke-methodrefs
               (filter implicit-cf?)
               not-empty)))))

(defn implicit-cf-class?
  "test whether class possibly contains implicit cf"
  [class]
  (->> class get-transitive-implicit-cf-super-class-and-interface not-empty))

(def implicit-cf?
  "test whether methodref is possibly an implicit cf"
  get-implicit-cf-root-class-names)

(defn implicit-cf-task?
  [method]
  (set/intersection (->> method get-implicit-cf-root-class-names)
                    (set (->> implicit-cf-marker-task keys))))

(defn implicit-cf-component?
  [method]
  (set/intersection (->> method get-implicit-cf-root-class-names)
                    (set (->> implicit-cf-marker-component keys))))

(defn get-transitive-implicit-cf-super-class-and-interface
  [class]
  (set/intersection (set (keys implicit-cf-marker))
                    (->> class
                         get-transitive-super-class-and-interface
                         (map get-soot-class-name)
                         set)))

(defn get-implicit-cf-root-class-names
  [method]
  (let [class (->> method get-soot-class)
        name (->> method get-soot-name)]
    (->> (get-transitive-implicit-cf-super-class-and-interface class)
         (filter #(let [t (get implicit-cf-marker %)]
                    (or (= t :all)
                        (contains? t name))))
         not-empty)))

;;
;; domain knowledge
;; 

(def ^:private implicit-cf-marker-task
  {"java.lang.Thread" #{"start"}
   "java.lang.Runnable" #{"run"}
   "java.util.concurrent.Callable" #{"call"}
   "java.util.concurrent.Executor" #{"execute"}
   "java.util.concurrent.ExecutorService" #{"submit"
                                            "execute"}
   "java.lang.Class" #{"forName"
                       "getMethod"
                       "getField"}
   "java.lang.reflect.Method" #{"invoke"}
   "java.lang.reflect.Field" :all
   "android.os.Handler" #{"post" "postAtFrontOfQueue"
                          "postAtTime" "postDelayed"}})

(def ^:private implicit-cf-marker-component
  {"android.content.Context" #{"startActivity" "startActivities"
                               "startService" "stopService"
                               "bindService" "unbindService"
                               "sendBroadcast" "sendBrocastAsUser"
                               "sendOrderedBroadcast" "sendOrderedBroadcastAsUser"
                               "sendStickyBroadcast" "sendStickyBroadcastAsUser"
                               "registerComponentCallbacks"
                               "registerReceiver"}})

(def ^:private implicit-cf-marker
  "these methods mark implicit control flows"
  (merge implicit-cf-marker-task
         implicit-cf-marker-component))

(def ^:private safe-invokes
  "safe classes are the ones that can be simulated in Clojure"
  {;;; java.lang
   ;; interface
   "java.lang.Iterable" :all
   ;; classes
   "java.lang.String" :all
   "java.lang.StringBuilder" :all
   "java.lang.StringBuffer" :all
   "java.lang.Math" :all
   "java.lang.StrictMath" :all
   "java.lang.Integer" :all
   "java.lang.Long" :all
   "java.lang.Double" :all
   "java.lang.Float" :all
   "java.lang.Byte" :all
   "java.lang.Character" :all
   "java.lang.Short" :all
   "java.lang.Boolean" :all
   "java.lang.Void" :all
   "java.lang.System" #{"nanoTime"
                        "currentTimeMillis"}
   ;;; java.util
   ;; interface
   "java.util.Collection" :all
   "java.util.Comparator" :all
   "java.util.Deque" :all
   "java.util.Enumeration" :all
   "java.util.Formattable" :all
   "java.util.Iterator" :all
   "java.util.List" :all
   "java.util.ListIterator" :all
   "java.util.Map" :all
   "java.util.Map$Entry" :all
   "java.util.NavigableMap" :all
   "java.util.NavigableSet" :all
   "java.util.Queue" :all
   "java.util.RandomAccess" :all
   "java.util.Set" :all
   "java.util.SortedMap" :all
   "java.util.SortedSet" :all
   ;; classes
   "java.util.ArrayList" :all
   "java.util.ArrayDeque" :all
   "java.util.Arrays" :all
   "java.util.BitSet" :all
   "java.util.Calendar" :all
   "java.util.Collections" :all
   "java.util.Currency" :all
   "java.util.Date" :all
   "java.util.Dictionary" :all
   "java.util.EnumMap" :all
   "java.util.EnumSet" :all
   "java.util.Formatter" :all
   "java.util.GregorianCalendar" :all
   "java.util.HashMap" :all
   "java.util.HashSet" :all
   "java.util.Hashtable" :all
   "java.util.IdentityHashMap" :all
   "java.util.LinkedHashMap" :all
   "java.util.LinkedHashSet" :all
   "java.util.LinkedList" :all
   "java.util.Locale" :all
   "java.util.Locale$Builder" :all
   "java.util.Objects" :all
   "java.util.PriorityQueue" :all
   "java.util.Properties" :all
   "java.util.Random" :all
   "java.util.SimpleTimeZone" :all
   "java.util.Stack" :all
   "java.util.StringTokenizer" :all
   "java.util.TreeMap" :all
   "java.util.TreeSet" :all
   "java.util.UUID" :all
   "java.util.Vector" :all
   "java.util.WeakHashMap" :all})
