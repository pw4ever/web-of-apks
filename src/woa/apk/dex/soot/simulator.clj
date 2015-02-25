(ns woa.apk.dex.soot.simulator
  ;; internal libs
  (:use woa.util)   
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
                 Scene)
           
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
         simulator-evaluate
         simulator-new-instance
         simulator-get-field simulator-set-field
         simulator-get-this simulator-get-param
         simulator-set-local simulator-get-local
         simulator-add-returns simulator-get-returns simulator-clear-returns
         simulator-add-explicit-invokes simulator-get-explicit-invokes simulator-clear-explicit-invokes
         simulator-add-implicit-invokes simulator-get-implicit-invokes simulator-clear-implicit-invokes
         simulator-add-component-invokes simulator-get-component-invokes simulator-clear-component-invokes
         simulator-add-invoke-paths simulator-get-invoke-paths simulator-clear-invoke-paths)
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
    (let [instance (simulator-resolve-value (.. field getBase)
                                            simulator)
          field (.. field getFieldRef)
          value (simulator-get-field instance field)]
      (if (= value :nil)
        (make-field-sexp instance field)
        (simulator-resolve-value value simulator)))))

(extend-type soot.jimple.StaticFieldRef
  SimulatorValueResolver
  (simulator-resolve-value [field simulator]
    (let [value (simulator-get-field nil field)]
      (if (= value :nil)
        (make-field-sexp nil field)
        (simulator-resolve-value value simulator)))))

(extend-type soot.jimple.NullConstant
  SimulatorValueResolver
  (simulator-resolve-value [_ simulator]
    nil))

(extend-type soot.jimple.ClassConstant
  SimulatorValueResolver
  (simulator-resolve-value [const simulator]
    (let [value (make-class-sexp (get-soot-class const))]
      value)))

(extend-type soot.jimple.Constant
  SimulatorValueResolver
  (simulator-resolve-value [const simulator]
    (let [value (try
                  (.. const value)
                  (catch Exception e
                    (make-constant-sexp const)))]
      value)))

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
      (aset base-value index-value value))))

;;
;; get method interesting invokes and helpers
;; 


(def ^:dynamic *init-instances*
  "initial instance of classes within circumscription"
  nil)
(def ^:dynamic *simulator-global-state*
  "simulator's global state "
  nil)
(defmacro with-simulator
  [& body]
  ;; initialized here to avoid unintended retention across different runs
  `(binding [*init-instances* (atom nil)
             *simulator-global-state* (atom nil)]
     ~@body))

(defn initialize-classes
  "initialize class by invoking <clinit>"
  [{:keys [classes circumscription]
    :or {circumscription :all}
    :as initialize-params}
   {:keys [verbose
           soot-debug-show-exceptions]
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
      (swap! *init-instances* assoc-in [(->> class get-soot-class-name)]
             (simulator-new-instance class))
      (doseq [^SootMethod clinit (.. (soot.EntryPoints/v) (clinitsOf class))]
        (try
          (simulate-method {:method clinit
                            :this nil
                            :params nil}
                           (assoc-in options [:circumscription]
                                     circumscription))
          (catch Exception e
            (when soot-debug-show-exceptions
              (print-stack-trace e))))))))

(defn get-all-interesting-invokes
  "get both explicit and implicit interesting invokes"
  [^SootMethod root-method
   interesting-method?
   circumscription
   {:keys [verbose
           soot-debug-show-exceptions]
    :as options}]
  (let [all-explicit-invokes (atom #{})
        all-implicit-invokes (atom #{})
        all-component-invokes (atom #{})
        all-invoke-paths (atom nil)
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
      (let [{:keys [returns
                    explicit-invokes
                    implicit-invokes
                    component-invokes
                    invoke-paths]}
            ;; full simulation
            (simulate-method {:method
                              root-method
                              :this
                              ;; use initial instance if available
                              (let [root-method-class (->> root-method get-soot-class)
                                    instance (get-in @*init-instances*
                                                     [(->> root-method get-soot-class-name)])]
                                (if instance
                                  instance
                                  (simulator-new-instance root-method-class)))
                              :params
                              (->> (.. root-method getParameterTypes)
                                   (map #(make-external-sexp %)))
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
               component-invokes)
        (reset! all-invoke-paths invoke-paths))
      (catch Exception e
        (when soot-debug-show-exceptions
          (print-stack-trace e))))
    ;; return result
    {:explicit-invokes @all-explicit-invokes
     :implicit-invokes @all-implicit-invokes
     :component-invokes @all-component-invokes
     :invoke-paths @all-invoke-paths}))

(defn- simulate-method
  "simulate method"
  [{:keys [method this params interesting-method?]
    :or {interesting-method? (constantly true)}
    :as simulation-params}
   {:keys [circumscription
           soot-basic-block-simulation-budget
           soot-method-simulation-depth-budget
           soot-debug-show-exceptions]
    :or {circumscription :all}
    :as options}]
  
  (let [method (try (soot-resolve method)
                    (catch Exception e method))
        method-name (try
                      (.. method getSignature)
                      (catch Exception e))
        default-return #{(make-invoke-sexp :invoke method this params)}]
    (cond
      (not (instance? soot.SootMethod method))
      {:returns default-return
       :explicit-invokes #{}
       :implicit-invokes #{}
       :component-invokes #{}
       :invoke-paths method-name}      
      
      ;; only simulate method within circumscription
      (and (not= circumscription :all)
           (not (contains? circumscription
                           (.. method getSignature))))
      (do
        {:returns default-return
         :explicit-invokes #{}
         :implicit-invokes #{}
         :component-invokes #{}
         :invoke-paths method-name})
      
      (< soot-method-simulation-depth-budget 0)
      (do
        {:returns #{(make-error-sexp :no-budget
                                     {:method method
                                      :this this
                                      :params params})}
         :explicit-invokes #{}
         :implicit-invokes #{}
         :component-invokes #{}
         :invoke-paths method-name})

      ;; no method body, cannot proceed
      (try
        (.. method retrieveActiveBody)
        false
        (catch Exception e
          true))
      (do
        {:returns #{(make-error-sexp :no-method-body
                                     {:method method
                                      :this this
                                      :params params})}
         :explicit-invokes #{}
         :implicit-invokes #{}
         :component-invokes #{}
         :invoke-paths method-name})

      :otherwise
      (let [all-returns (atom #{})
            all-explicit-invokes (atom #{})
            all-implicit-invokes (atom #{})
            all-component-invokes (atom #{})
            all-invoke-paths (atom (when method-name
                                     {method-name #{}}))
            
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
           ;; width-first search to prevent malicious code exhausting bb-budget
           (->> worklist
                (mapcat (fn [{:keys [simulator start-stmt]}]
                          (when (and @bb-budget
                                     (> @bb-budget 0))
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
                              (when method-name
                                (swap! all-invoke-paths update-in [method-name]
                                       into
                                       (-> simulator
                                           simulator-get-invoke-paths)))
                              ;; add the following to worklist
                              (for [start-stmt next-start-stmts]
                                ;; control flow sensitive!
                                {:simulator (-> simulator
                                                simulator-clear-returns
                                                simulator-clear-explicit-invokes
                                                simulator-clear-implicit-invokes
                                                simulator-clear-component-invokes
                                                simulator-clear-invoke-paths)
                                 :start-stmt start-stmt}))))))))
        {:returns @all-returns
         :explicit-invokes @all-explicit-invokes
         :implicit-invokes @all-implicit-invokes
         :component-invokes @all-component-invokes
         :invoke-paths (if (empty? (get-in @all-invoke-paths [method-name]))
                         method-name
                         @all-invoke-paths)}))))

(defn- simulate-basic-block
  "simulate a basic block"
  [{:keys [simulator stmt-info start-stmt method interesting-method?]
    :as simulation-params}
   {:keys [soot-method-simulation-depth-budget
           soot-simulation-conservative-branching
           soot-simulation-linear-scan
           soot-debug-show-each-statement
           soot-debug-show-locals-per-statement
           soot-debug-show-all-per-statement
           soot-debug-show-exceptions
           verbose]
    :as options}]
  (let [simulator (atom simulator)
        
        [basic-block residue]
        (split-with (if soot-simulation-linear-scan
                      ;; linear scan do not split at branching
                      (constantly true)
                      ;; otherwise, split at first branch or return
                      #(let [^Stmt stmt %]
                         (and (.. stmt fallsThrough)
                              (not (.. stmt branches)))))
                    (subvec (:stmts stmt-info)
                            (get (:stmt-2-index stmt-info)
                                 start-stmt)))]
    ;; simulate statements in the basic block
    (doseq [^Stmt stmt basic-block]

      (try
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
                           (when soot-debug-show-exceptions
                             (print-stack-trace e)))))
                     (caseIfStmt [stmt])
                     (caseInvokeStmt [stmt]
                       (try
                         (-> (.. stmt getInvokeExpr)
                             (simulator-evaluate {:simulator simulator
                                                  :interesting-method?
                                                  interesting-method?}
                                                 options))
                         (catch Exception e
                           (when soot-debug-show-exceptions
                             (print-stack-trace e)))))
                     (caseLookupSwitchStmt [stmt])
                     (caseNopStmt [stmt])
                     (caseRetStmt [stmt])
                     (caseReturnStmt [stmt])
                     (caseReturnVoidStmt [stmt])
                     (caseTableSwitchStmt [stmt])
                     (caseThrowStmt [stmt])
                     (defaultCase [stmt]))))
        (catch Exception e
          (when soot-debug-show-exceptions
            (print-stack-trace e))))
      (when (or soot-debug-show-each-statement
                soot-debug-show-locals-per-statement
                soot-debug-show-all-per-statement)
        (println stmt)
        (when (or soot-debug-show-locals-per-statement
                  soot-debug-show-all-per-statement)
          (println "- locals -")
          (pprint (:locals @simulator))
          (when soot-debug-show-all-per-statement
            (println "- globals -")
            (pprint @*simulator-global-state*))
          (println "----------"))))
    (let [return (atom {:simulator nil ; to be filled at the end
                        :next-start-stmts nil})
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

                         (if soot-simulation-conservative-branching
                           ;; conservative branching
                           ;; senstive to value
                           ;; good: exact, eliminate dead branch
                           ;; bad: may not cover enough branches when budget depelete
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
                                      conj stmt)))
                           ;; aggresive branching
                           ;; insensitive to value
                           ;; good: cover as much branches as possible
                           ;; bad: not exact, may get into dead branch
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
   explicit-invokes implicit-invokes component-invokes invoke-paths])

(defn- create-simulator
  [this params]
  (map->Simulator {:this this
                   :params (vec params)
                   :locals {}
                   :returns #{}
                   :explicit-invokes #{}
                   :implicit-invokes #{}
                   :component-invokes #{}
                   :invoke-paths #{}}))

(defn- simulator-new-instance
  [& [class]]
  (let [instance (gensym (str "instance"
                              (when-let [class-name (get-soot-class-name class)]
                                (str "-" class-name "-"))))]
    (make-instance-sexp class instance)))

(defn- simulator-evaluate
  "evaluate expr in simulator (simulator should be an Clojure atom to allow updates)"
  [expr
   {:keys [simulator interesting-method?]
    :as simulation-params}
   {:keys [soot-method-simulation-depth-budget
           soot-simulation-collection-size-budget
           soot-no-implicit-cf
           soot-dump-all-invokes
           soot-debug-show-implicit-cf
           soot-debug-show-safe-invokes
           soot-debug-show-exceptions
           layout-callbacks
           verbose]
    :as options}]
  (let [result (atom nil)

        ;; binary operation
        binary-operator-expr
        (fn [expr operator operator-name]
          (let [op1 (-> (.. expr getOp1) (simulator-resolve-value @simulator) int)
                op2 (-> (.. expr getOp2) (simulator-resolve-value @simulator) int)
                default-return (make-binary-operator-sexp operator-name
                                                          [op1 op2])]
            (try
              (operator op1 op2)
              (catch Exception e
                (when soot-debug-show-exceptions
                  (print-stack-trace e))
                default-return))))
        
        ;; unary operation
        unary-operator-expr
        (fn [expr operator operator-name]
          (let [op (-> (.. expr getOp) (simulator-resolve-value @simulator) int)
                default-return (make-unary-operator-sexp operator-name
                                                         [op])]
            (try
              (operator op)
              (catch Exception e
                (when soot-debug-show-exceptions
                  (print-stack-trace e))
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
                         [{:method method
                           :args args}])))

              (let [invoke-method (fn [method this params & [implicit?]]
                                    (try
                                      ;; try resolve method
                                      (soot-resolve method)
                                      (let [{:keys [returns
                                                    explicit-invokes
                                                    implicit-invokes
                                                    component-invokes
                                                    invoke-paths]}
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
                                                   component-invokes)
                                            (swap! simulator-add-invoke-paths
                                                   #{invoke-paths}))
                                          ;; if the result is unique, extract it
                                          (if (== 1 (count returns))
                                            (first returns)
                                            returns)))                                      
                                      
                                      (catch Exception e)
                                      (finally
                                        (when (or soot-dump-all-invokes
                                                  (try
                                                    (interesting-method? method)
                                                    (catch Exception e)))
                                          (doto simulator
                                            (swap! (if implicit?
                                                     simulator-add-implicit-invokes
                                                     simulator-add-explicit-invokes)
                                                   [{:method method
                                                     :args params}]))))))]
                (cond
                  
                  ;; safe invokes
                  (let [t (get safe-invokes class-name)]
                    (or (= t :all)
                        (contains? t method-name)))
                  (try
                    (when soot-debug-show-safe-invokes
                      (println "safe invoke:"
                               class-name base-value method-name args))                    
                    (let [result (case invoke-type
                                   :special-invoke
                                   (simulator-assign
                                    base
                                    (clojure.lang.Reflector/invokeConstructor (Class/forName class-name)
                                                                              (object-array args))
                                    simulator)

                                   :static-invoke
                                   (clojure.lang.Reflector/invokeStaticMethod class-name
                                                                              method-name
                                                                              (object-array args))

                                   ;; otherwise
                                   (clojure.lang.Reflector/invokeInstanceMethod base-value
                                                                                method-name
                                                                                (object-array args)))]
                      (when soot-debug-show-safe-invokes
                        (println "safe invoke result:"
                                 result))
                      (if (and (instance? java.util.Collection result)
                               (> (.size result) soot-simulation-collection-size-budget))
                        default-return
                        result))
                    (catch Exception e
                      default-return))

                  ;; setContentView
                  (#{"setContentView"} method-name)
                  (let [layout-id (first args)]
                    (cond
                      (number? layout-id)
                      (doseq [{:keys [method]
                               :as layout-callback}
                              (get layout-callbacks layout-id)]
                        (when layout-callback
                          (let [info (dissoc layout-callback :method)]
                            (try
                              (doseq [the-method (find-method-candidates method-class
                                                                         method
                                                                         [info])]
                                (invoke-method the-method base-value [info])) 
                              (catch Exception e
                                default-return)))))

                      :otherwise
                      default-return))

                  ;; special-invokes
                  (= invoke-type :special-invoke)
                  (try
                    (cond
                      ;; Runnable is the one to be run
                      (and (transitive-ancestor? "java.lang.Thread" method-class)
                           (first args))
                      (simulator-assign base (first args) simulator)

                      :otherwise
                      (simulator-assign base
                                        (simulator-new-instance method-class)
                                        simulator))
                    default-return
                    (catch Exception e
                      default-return))

                  ;; implicit cf: task
                  (and (not soot-no-implicit-cf)
                       (implicit-cf-task? method))
                  (try
                    (let [root-class-name (->> method
                                               get-implicit-cf-root-class-names
                                               first)
                          x [root-class-name method-name]]
                      (when soot-debug-show-implicit-cf
                        (println "implicit cf:" x base-value args))
                      (cond
                        (#{["java.lang.Thread" "start"]
                           ["java.lang.Runnable" "run"]}
                         x)
                        (do
                          (doseq [implicit-target
                                  (find-method-candidates (get-soot-class base-value)
                                                          "run"
                                                          [])]
                            (when soot-debug-show-implicit-cf
                              (println (format "implicit cf to: %1$s.%2$s:"
                                               root-class-name method-name)
                                       method-class
                                       base-value
                                       implicit-target))
                            (invoke-method implicit-target base-value [] true)))

                        (#{["java.util.concurrent.Callable" "call"]}
                         x)
                        (doseq [implicit-target (find-method-candidates method-class
                                                                        "call"
                                                                        [])]
                          (when soot-debug-show-implicit-cf
                            (println (format "implicit cf to: %1$s.%2$s:"
                                             root-class-name method-name)
                                     method-class
                                     base-value
                                     implicit-target))                          
                          (invoke-method implicit-target base-value [] true))

                        (#{["java.util.concurrent.Executor" "execute"]
                           ["java.util.concurrent.ExecutorService" "execute"]}
                         x)
                        (let [target-obj (first args)]
                          (doseq [implicit-target
                                  (find-method-candidates (get-soot-class target-obj)
                                                          "run"
                                                          [])]
                            (when soot-debug-show-implicit-cf
                              (println (format "implicit cf to: %1$s.%2$s:"
                                               root-class-name method-name)
                                       method-class
                                       base-value
                                       implicit-target))                          
                            (invoke-method implicit-target target-obj [] true)))

                        (#{["java.util.concurrent.ExecutorService" "submit"]}
                         x)
                        (let [target-obj (first args)]
                          (doseq [implicit-target
                                  (find-method-candidates (get-soot-class target-obj)
                                                          "run"
                                                          [])]
                            (when soot-debug-show-implicit-cf
                              (println (format "implicit cf to: %1$s.%2$s:"
                                               root-class-name method-name)
                                       method-class
                                       base-value
                                       implicit-target))                            
                            (invoke-method implicit-target target-obj [] true))
                          (doseq [implicit-target
                                  (find-method-candidates (get-soot-class target-obj)
                                                          "call"
                                                          [])]
                            (when soot-debug-show-implicit-cf
                              (println (format "implicit cf to: %1$s.%2$s:"
                                               root-class-name method-name)
                                       method-class
                                       base-value
                                       implicit-target))                            
                            (invoke-method implicit-target target-obj [] true)))

                        (#{["android.os.Handler" "post"]
                           ["android.os.Handler" "postAtFrontOfQueue"]
                           ["android.os.Handler" "postAtTime"]
                           ["android.os.Handler" "postDelayed"]}
                         x)
                        (let [target-obj (first args)]
                          (doseq [implicit-target
                                  (find-method-candidates (get-soot-class target-obj)
                                                          "run"
                                                          [])]
                            (when soot-debug-show-implicit-cf
                              (println (format "implicit cf to: %1$s.%2$s:"
                                               root-class-name method-name)
                                       method-class
                                       base-value
                                       implicit-target))
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
                            ;; there could be more than one such method
                            (let [candidates
                                  (find-method-candidates (get-soot-class base-value)
                                                          (str target-obj)
                                                          (count (second args)))]
                              (if-not (empty? candidates)
                                candidates
                                (make-method-sexp base-value target-obj)))
                            (catch Exception e
                              (make-method-sexp base-value target-obj))))

                        (#{["java.lang.reflect.Method" "invoke"]}
                         x)
                        (try
                          (let [result (atom #{})]
                            (if-not (instance? woa.apk.dex.soot.sexp.Sexp
                                               base-value)
                              ;; try candidates
                              (doseq [method base-value]
                                (let [invoke-instance (first args)
                                      invoke-args (second args)]
                                  (when (= (count invoke-args)
                                           (.. method getParameterCount))
                                    (when soot-debug-show-implicit-cf
                                      (println (format "implicit cf to: %1$s.%2$s:"
                                                       root-class-name method-name)
                                               method
                                               invoke-instance
                                               invoke-args))
                                    (when-let [r (try
                                                   (invoke-method method
                                                                  invoke-instance
                                                                  invoke-args
                                                                  true)
                                                   (catch Exception e))]
                                      (swap! result conj r)))))
                              ;; otherwise, MethodSexp
                              (do
                                (doto simulator
                                  (swap! simulator-add-implicit-invokes
                                         [{:method base-value
                                           :args (second args)}]))
                                (try
                                  (doto simulator
                                    (swap! simulator-add-invoke-paths
                                           #{(format "%1$s.%2$s[%3$d args]"
                                                     (get-soot-class-name base-value)
                                                     (get-soot-name base-value)
                                                     (count (second args)))}))
                                  (catch Exception e))
                                (swap! result conj
                                       (make-invoke-sexp :reflect base-value
                                                         (first args) (vec (second args))))))
                            (first result))
                          (catch Exception e
                            (make-invoke-sexp :reflect base-value
                                              (first args) (vec (second args)))))
                        
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
                          (let [field base-value
                                value (simulator-get-field nil base-value)]
                            value)
                          (catch Exception e
                            (make-field-sexp (simulator-get-this @simulator) base-value)))

                        (and (= "java.lang.reflect.Field" root-class-name)
                             (#{"equals"}) method-name)
                        (try
                          (let [field base-value
                                value (simulator-get-field nil field)]
                            (= value (first args)))
                          (catch Exception e
                            (make-field-sexp (simulator-get-this @simulator)
                                             base-value)))

                        (and (= "java.lang.reflect.Field" root-class-name)
                             (#{"set" "setBoolean" "setByte" "setChar"
                                "setDouble" "setFloat" "setInt" "setLong" "setShort"}
                              method-name))
                        (try
                          (let [field base-value
                                value (first args)]
                            (simulator-set-field nil field value)
                            value)
                          (catch Exception e
                            (make-field-sexp (simulator-get-this @simulator) base-value)))

                        :default default-return))
                    (catch Exception e
                      default-return))

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

                        
                        :default default-return))
                    (catch Exception e
                      default-return))

                  :default
                  (invoke-method method base-value args)))
              
              (catch Exception e
                default-return)
              (finally
                (try
                  (doto simulator
                    (swap! simulator-add-invoke-paths
                           #{(.. method getSignature)}))
                  (catch Exception e))))))

        cast-expr
        (fn [expr]
          (let [value (-> (.. expr getOp) (simulator-resolve-value @simulator))
                cast-type (.. expr getCastType)
                default-return (make-cast-sexp value cast-type)]
            (try
              (let [result ((cond
                              (instance? soot.BooleanType cast-type)
                              boolean
                              
                              (instance? soot.ByteType cast-type)
                              byte

                              (instance? soot.CharType cast-type)
                              char

                              (instance? soot.ShortType cast-type)
                              short

                              (instance? soot.IntType cast-type)
                              int

                              (instance? soot.LongType cast-type)
                              long

                              (instance? soot.FloatType cast-type)
                              float

                              (instance? soot.DoubleType cast-type)
                              double
                              
                              :otherwise
                              identity)
                            value)]
                result)
              (catch Exception e default-return))))

        new-array-expr
        (fn [expr]
          (let [base-type (.. expr getBaseType)
                size (-> (.. expr getSize) (simulator-resolve-value @simulator))
                default-return (make-new-array-sexp base-type size)]
            (try
              (let [result
                    (if (< size soot-simulation-collection-size-budget)
                      ((cond
                         (instance? soot.BooleanType base-type)
                         boolean-array
                         
                         (instance? soot.ByteType base-type)
                         byte-array

                         (instance? soot.CharType base-type)
                         char-array

                         (instance? soot.ShortType base-type)
                         short-array

                         (instance? soot.IntType base-type)
                         int-array

                         (instance? soot.LongType base-type)
                         long-array

                         (instance? soot.FloatType base-type)
                         float-array

                         (instance? soot.DoubleType base-type)
                         double-array
                         
                         :otherwise
                         object-array)
                       size)                      
                      default-return)]
                result)
              (catch Exception e default-return))))

        new-multi-array-expr
        (fn [expr]
          (let [base-type (.. expr getBaseType)
                sizes (->> (.. expr getSizes)
                           (map #(simulator-resolve-value % @simulator)))
                size (reduce * sizes)
                default-return (make-new-array-sexp base-type sizes)]
            (try
              (let [result
                    (if (< size
                           soot-simulation-collection-size-budget)
                      (apply make-array
                             (cond
                               (instance? soot.BooleanType base-type)
                               Boolean/TYPE
                               
                               (instance? soot.ByteType base-type)
                               Byte/TYPE

                               (instance? soot.CharType base-type)
                               Character/TYPE

                               (instance? soot.ShortType base-type)
                               Short/TYPE

                               (instance? soot.IntType base-type)
                               Integer/TYPE

                               (instance? soot.LongType base-type)
                               Long/TYPE

                               (instance? soot.FloatType base-type)
                               Float/TYPE

                               (instance? soot.DoubleType base-type)
                               Double/TYPE
                               
                               :otherwise
                               Object)
                             sizes)                      
                      default-return)]
                result)
              (catch Exception e default-return))))]
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
                       (binary-operator-expr expr + :add)))
             (caseAndExpr [expr]
               (reset! result
                       (binary-operator-expr expr bit-and :and)))
             (caseCastExpr [expr]
               (reset! result
                       (cast-expr expr)))
             (caseCmpExpr [expr]
               (reset! result
                       (binary-operator-expr expr compare :cmp)))
             (caseCmpgExpr [expr]
               ;; JVM-specific artifacts; N/A on Dalvik
               (reset! result
                       (binary-operator-expr expr compare :cmpg)))
             (caseCmplExpr [expr]
               ;; JVM-specific artifacts; N/A on Dalvik
               (reset! result
                       (binary-operator-expr expr compare :cmpl)))
             (caseDivExpr [expr]
               (reset! result
                       (binary-operator-expr expr / :div)))
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
                            (make-binary-operator-sexp == [op1 op2])))
                        :eq)))
             (caseGeExpr [expr]
               (reset! result
                       (binary-operator-expr expr >= :ge)))
             (caseGtExpr [expr]
               (reset! result
                       (binary-operator-expr expr > :gt)))
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
                             (when soot-debug-show-exceptions
                               (print-stack-trace e))
                             default-return)))))
             (caseInterfaceInvokeExpr [expr]
               (reset! result
                       (invoke-expr :interface-invoke
                                    (.. expr getMethodRef)
                                    (.. expr getBase)
                                    (.. expr getArgs))))
             (caseLeExpr [expr]
               (reset! result
                       (binary-operator-expr expr <= :le)))
             (caseLengthExpr [expr]
               (reset! result
                       (unary-operator-expr expr count :length)))
             (caseLtExpr [expr]
               (reset! result
                       (binary-operator-expr expr < :lt)))
             (caseMulExpr [expr]
               (reset! result
                       (binary-operator-expr expr * :mul)))
             (caseNeExpr [expr]
               (reset! result
                       ;; only non-sexp can be meaningfully compared                       
                       (binary-operator-expr
                        expr
                        (fn [op1 op2]
                          (if (and (not (extends? Sexp (class op1)))
                                   (not (extends? Sexp (class op2))))
                            (not= op1 op2)
                            (make-binary-operator-sexp not= [op1 op2])))
                        :ne)))
             (caseNegExpr [expr]
               (reset! result
                       (unary-operator-expr expr - :neg)))
             (caseNewArrayExpr [expr]
               (reset! result
                       (new-array-expr expr)))
             (caseNewExpr [expr]
               ;; will be evaluated in caseSpecialInvokeExpr where the arguments are ready
               )
             (caseNewMultiArrayExpr [expr]
               (reset! result
                       (new-multi-array-expr expr)))
             (caseOrExpr [expr]
               (reset! result
                       (binary-operator-expr expr bit-or :or)))
             (caseRemExpr [expr]
               (reset! result
                       (binary-operator-expr expr rem :rem)))
             (caseShlExpr [expr]
               (reset! result
                       (binary-operator-expr expr not= :shl)))
             (caseShrExpr [expr]
               (reset! result
                       (binary-operator-expr expr bit-shift-right :shr)))
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
                       (binary-operator-expr expr - :sub)))
             (caseUshrExpr [expr]
               (reset! result
                       (binary-operator-expr expr unsigned-bit-shift-right :ushr)))
             (caseVirtualInvokeExpr [expr]
               (reset! result
                       (invoke-expr :virtual-invoke
                                    (.. expr getMethodRef)
                                    (.. expr getBase)
                                    (.. expr getArgs))))
             (caseXorExpr [expr]
               (reset! result
                       (binary-operator-expr expr bit-xor :xor)))
             ;; RefSwitch
             (caseArrayRef [ref]
               (reset! result
                       (let [base (-> (.. ref getBase) (simulator-resolve-value @simulator))
                             index (-> (.. ref getIndex) (simulator-resolve-value @simulator))
                             default-return (make-array-ref-sexp base index)]
                         (try
                           (aget base index)
                           (catch Exception e
                             (when soot-debug-show-exceptions
                               (print-stack-trace e))
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
        (when soot-debug-show-exceptions
          (print-stack-trace e))))
    @result))

;; :nil signify N/A
(defn- simulator-get-field
  [instance field]
  (let [field (-> field soot-resolve)
        class-name (-> field get-soot-class-name)
        field-name (-> field get-soot-name)
        field-id [class-name field-name]
        instance (cond
                   (instance? woa.apk.dex.soot.sexp.InstanceSexp instance)
                   (:instance instance)
                   
                   :otherwise instance)]
    (if (.. field isStatic)
      (get-in @*simulator-global-state* [:fields :static field-id] :nil)
      (get-in @*simulator-global-state* [:fields :instance instance field-id] :nil))))

(defn- simulator-set-field
  [instance field value]
  (let [field (-> field soot-resolve)
        class-name (-> field get-soot-class-name)
        field-name (-> field get-soot-name)
        field-id [class-name field-name]
        instance (cond
                   (instance? woa.apk.dex.soot.sexp.InstanceSexp instance)
                   (:instance instance)
                   
                   :otherwise instance)]
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

(defn- simulator-add-invoke-paths
  [simulator invokes]
  (update-in simulator [:invoke-paths] into
             invokes))

(defn- simulator-get-invoke-paths
  [simulator]
  (get-in simulator [:invoke-paths]))

(defn- simulator-clear-invoke-paths
  [simulator]
  (assoc-in simulator [:invoke-paths] #{}))

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
