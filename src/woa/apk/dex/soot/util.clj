(ns woa.apk.dex.soot.util
  ;; internal libs
  (:use woa.util)
  ;; common libs
  (:require [clojure.string :as str]
            [clojure.set :as set]
            [clojure.walk :as walk]
            [clojure.zip :as zip]
            [clojure.java.io :as io]
            [clojure.pprint :refer [pprint print-table]]
            [clojure.stacktrace :refer [print-stack-trace]])
  ;; import
  (:import
   (soot G
         G$GlobalObjectGetter
         PhaseOptions
         PackManager
         Scene

         Pack
         Unit
         SootClass
         SootMethod
         SootMethodRef)
   (soot.options Options)
   (soot.jimple Stmt)))

;;; declaration

(declare soot-queryable?)
(declare find-method-candidates)
(declare get-application-classes get-application-methods)
(declare get-method-body map-class-bodies run-body-packs)
(declare mapcat-invoke-methodrefs resolve-methodrefs mapcat-invoke-methods)
(declare get-transitive-super-class-and-interface
         get-interesting-transitive-super-class-and-interface
         transitive-ancestor?)
(declare filter-interesting-methods)
(declare get-cg mapcat-edgeout-methods)
(declare android-api?)
(declare with-soot new-g-objgetter)
(declare mute unmute with-silence)

;;; implementation

;;
;; SootQuery
;; 

(defprotocol SootQuery
  (get-soot-class [this])
  (get-soot-class-name [this])
  (get-soot-name [this])
  (soot-resolve [this]))

(defn soot-queryable?
  "test whether SottQuery can be applied on cand without Exception"
  [cand]
  (try
    (let [class (-> cand get-soot-class)]
      (-> cand get-soot-name)
      (-> cand get-soot-class-name)
      (.. class getPackageName)
      true)
    (catch Exception e
      false)))

(extend-type nil
  SootQuery
  (get-soot-class [this]
    nil)
  (get-soot-class-name [this]
    nil)
  (get-soot-name [this]
    nil)
  (soot-resolve [this]
    nil))

(extend-type soot.SootClass
  SootQuery
  (get-soot-class [this]
    this)
  (get-soot-class-name [this]
    (get-soot-name this))
  (get-soot-name [this]
    (.. this getName))
  (soot-resolve [this]
    this))

(extend-type soot.SootMethod
  SootQuery
  (get-soot-class [this]
    (.. this getDeclaringClass))
  (get-soot-class-name [this]
    (->> this get-soot-class get-soot-name))
  (get-soot-name [this]
    (.. this getName))
  (soot-resolve [this]
    this))

(extend-type soot.SootMethodRef
  SootQuery
  (get-soot-class [this]
    (.. this declaringClass))
  (get-soot-class-name [this]
    (->> this get-soot-class get-soot-name))
  (get-soot-name [this]
    (.. this name))
  (soot-resolve [this]
    (.. this resolve)))

(extend-type soot.SootField
  SootQuery
  (get-soot-class [this]
    (.. this getDeclaringClass))
  (get-soot-class-name [this]
    (->> this get-soot-class get-soot-name))
  (get-soot-name [this]
    (.. this getName))
  (soot-resolve [this]
    this))

(extend-type soot.SootFieldRef
  SootQuery
  (get-soot-class [this]
    (.. this declaringClass))
  (get-soot-class-name [this]
    (->> this get-soot-class get-soot-name))
  (get-soot-name [this]
    (.. this name))
  (soot-resolve [this]
    (.. this resolve)))

(extend-type String
  SootQuery
  (get-soot-class [this]
    (.. (Scene/v) (getSootClass this)))
  (get-soot-class-name [this]
    this)
  (get-soot-name [this]
    this)
  (soot-resolve [this]
    ;; only Class string can be reasonably resolved
    (get-soot-class this)))

(extend-type soot.jimple.ClassConstant
  SootQuery
  (get-soot-class [this]
    (->> (.. this getValue) get-soot-class))
  (get-soot-class-name [this]
    (.. this getValue))
  (get-soot-name [this]
    (->> this get-soot-class-name))
  (soot-resolve [this]
    (->> this get-soot-class)))

(extend-type soot.RefType
  SootQuery
  (get-soot-class [this]
    (.. this getSootClass))
  (get-soot-class-name [this]
    (.. this getClassName))
  (get-soot-name [this]
    (->> this get-soot-class-name))
  (soot-resolve [this]
    (->> this get-soot-class)))

(extend-type soot.ArrayType
  SootQuery
  (get-soot-class [this]
    (->> (.. this getArrayElementType) get-soot-class))
  (get-soot-class-name [this]
    (->> this get-soot-class get-soot-name))
  (get-soot-name [this]
    (->> this get-soot-class-name))
  (soot-resolve [this]
    (->> this get-soot-class)))

(extend-type soot.jimple.FieldRef
  SootQuery
  (get-soot-class [this]
    (->> (.. this getFieldRef) get-soot-class))
  (get-soot-class-name [this]
    (->> this get-soot-class get-soot-name))
  (get-soot-name [this]
    (->> (.. this getFieldRef) get-soot-name))
  (soot-resolve [this]
    (.. this getField)))


;;
;; Soot Method helper
;; 

(defn find-method-candidates
  "args=nil: all method of the-class with method-name; otherwise: match by argument numbers"
  [the-class method-name args]
  (when-let [methods (not-empty
                      (->> (.. the-class getMethods)
                           (filter #(= (->> % get-soot-name)
                                       method-name))))]
    (cond
      (nil? args)
      methods
      
      :otherwise
      (->> methods
           (filter #(= (if (number? args) args (count args))
                       (.. ^SootMethod % getParameterCount)))))))

;;
;; Soot Class helpers
;; 

(defn get-application-classes
  "get application classes in scene"
  [scene]
  (->> (.. scene getApplicationClasses snapshotIterator)
       iterator-seq
       set))

(defn get-application-methods
  "get application methods in scene"
  [scene]
  (->> scene
       get-application-classes
       (mapcat #(try
                  (.. ^SootClass % getMethods)
                  (catch Exception e nil)))
       set))

;;
;; Soot Body helpers
;; 

(defn get-method-body
  "get method body"
  [^SootMethod method]
  (if (.. method hasActiveBody)
    (.. method getActiveBody)
    (when (and (not (.. method isPhantom))
               ;; method must have backing source
               (.. method getSource))
      (.. method retrieveActiveBody))))

(defn map-class-bodies
  "map classes to their method bodies"
  [classes]
  (->> classes
       (remove #(.. ^SootClass % isPhantom))
       (mapcat #(->> (.. ^SootClass % getMethods)
                     seq
                     (map get-method-body)
                     (filter identity)))))

(defn run-body-packs
  "run body packs over application classes"
  [& {:keys [scene pack-manager body-packs verbose]}]
  (doto scene
    (.loadNecessaryClasses))
  ;; force application class bodies to be mapped at least once 
  (let [bodies (->> scene get-application-classes map-class-bodies)
        packs (->> body-packs (map #(.. ^PackManager pack-manager (getPack ^String %))))]
    (doseq [^Pack pack packs]
      (when pack
        (doseq [^SootBody body bodies]
          (try
            (.. pack (apply body))
            ;; catch Exception to prevent it destroys outer threads
            (catch Exception e
              (print-stack-trace-if-verbose e verbose))))))))

;;
;; invoker-invokee relationship helpers
;; 

;; phantom SootClass has SootMethodRef but not SootMethod

(defn mapcat-invoke-methodrefs
  "mapcat methods to their invoked methodrefs"
  [methods]
  (->> methods
       (remove #(.. ^SootMethod % isPhantom))
       ;; try retrieveActiveBody
       (filter #(try
                  (.. ^SootMethod % retrieveActiveBody)
                  true
                  (catch Exception e
                    false)))
       (mapcat #(iterator-seq (.. ^SootMethod % retrieveActiveBody getUnits snapshotIterator)))
       (filter #(.. ^Stmt % containsInvokeExpr))
       (map #(.. ^Stmt % getInvokeExpr getMethodRef))))

(defn mapcat-invoke-methods
  "mapcat methods to their invoked methods"
  [methods]
  (->> methods
       mapcat-invoke-methodrefs
       ;; deduplication early
       set
       resolve-methodrefs
       set))

(defn resolve-methodrefs
  "resolve methodrefs"
  [methodrefs]
  (->> methodrefs
       (remove #(.. ^SootMethodRef % declaringClass isPhantom))
       (filter #(try
                  (.. ^SootMethodRef % resolve)
                  true
                  (catch Exception e
                    false)))
       (map #(.. ^SootMethodRef % resolve))))

;;
;; interesting method helpers
;; 

(defn filter-interesting-methods
  "filter interesting methodrefs"
  [interesting-method? methods]
  (->> methods
       (filter interesting-method?)))

;;
;; Soot callgraph helpers
;; 

(defn get-cg
  "get Call Graph from scene"
  [scene]
  (when (.. scene hasCallGraph)
    (.. scene getCallGraph)))

(defn mapcat-edgeout-methods
  "mapcat methods to their edgeout methods on cg "
  [methods cg]
  (when cg
    (->> methods
         (mapcat #(iterator-seq (.. ^soot.jimple.toolkits.callgraph.CallGraph cg (edgesOutOf %))))
         (map #(.. ^soot.jimple.toolkits.callgraph.Edge % getTgt))
         set)))

;;
;; helpers
;;

(defn android-api?
  "test see if obj is Android API"
  [obj]
  (re-find #"^(android\.|com\.android\.|dalvik\.)"
           (-> obj get-soot-class-name)))

;;
;; Soot body wrapper
;; 

(def soot-mutex
  "Soot mutex: Soot is unfortunately Singleton"
  (Object.))

(def system-security-manager
  "System's exsiting security manager"
  (System/getSecurityManager))

(def noexit-security-manager
  "prevent Soot brining down the system with System.exit"
  ;; http://stackoverflow.com/questions/21029651/security-manager-in-clojure/21033599#21033599
  (proxy [SecurityManager] []
    (checkPermission
      ([^java.security.Permission perm]
       (when (.startsWith (.getName perm) "exitVM")
         (throw (SecurityException. "no exit for Soot"))))
      ([^java.security.Permission perm ^Object context]
       (when (.startsWith (.getName perm) "exitVM")
         (throw (SecurityException. "no exit for Soot")))))))

;; this memoized function is initilized in with-soot
(def get-transitive-super-class-and-interface
  "get transitive super class and interfaces known to Soot"
  nil)

;; this memoized function is initilized in with-soot
(def get-interesting-transitive-super-class-and-interface
  "get interesting transitive super class and interfaces known to Soot"
  nil)

;; this memoized function is initilized in with-soot
(def transitive-ancestor?
  "name-or-class-a is a transitive ancestor (super class/interface) of class-b"
  nil)

(defn new-g-objgetter
  "create a new Soot context (G$GlobalObjectGetter)"
  []
  (let [g (new G)]
    (reify G$GlobalObjectGetter
      (getG [this] g)
      (reset [this]))))

(defmacro with-soot
  "wrap body with major Soot refs *at the call time*: g, scene, pack-manager, options, phase-options; g can be (optionally) provided with g-objgetter (nil to ask fetch the G *at the call time*); (G/reset) at the end if \"reset?\" is true"
  [g-objgetter reset? & body]
  `(locking soot-mutex
     
     (let [get-transitive-super-class-and-interface#
           (memoize
            (fn [class-or-interface#]
              ;; preserve order
              (let [known# (atom [])
                    class-or-interface# (get-soot-class class-or-interface#)]
                (loop [worklist# #{class-or-interface#}
                       visited# #{}]
                  (when-not (empty? worklist#)
                    (let [new-worklist# (atom #{})]
                      (doseq [item# worklist#
                              :when (not (visited# item#))]
                        (swap! known# conj item#)
                        ;; interfaces
                        (swap! new-worklist# into (->> (.. item# getInterfaces snapshotIterator)
                                                       iterator-seq))
                        ;; superclass?
                        (when (.. item# hasSuperclass)
                          (swap! new-worklist# conj (.. item# getSuperclass))))
                      (recur (set/difference @new-worklist# worklist#)
                             (set/union visited# worklist#)))))
                @known#)))
           
           get-interesting-transitive-super-class-and-interface#
           (memoize
            (fn [class-or-interface# interesting?#]
              ;; preserve order
              (let [known# (atom [])
                    class-or-interface# (get-soot-class class-or-interface#)]
                (loop [worklist# #{class-or-interface#}
                       visited# #{}]
                  (when-not (empty? worklist#)
                    (let [new-worklist# (atom #{})]
                      (doseq [item# worklist#
                              :when (not (visited# item#))]
                        (if (interesting?# item#)
                          ;; found the most close interesting ancestor: do not follow its ancestors
                          (swap! known# conj item#)
                          ;; otherwise, follow its ancestors
                          (do
                            ;; interfaces
                            (swap! new-worklist# into (->> (.. item# getInterfaces snapshotIterator)
                                                           iterator-seq))
                            ;; superclass?
                            (when (.. item# hasSuperclass)
                              (swap! new-worklist# conj (.. item# getSuperclass))))))
                      (recur (set/difference @new-worklist# worklist#)
                             (set/union visited# worklist#)))))
                @known#)))           
           
           transitive-ancestor?#
           (memoize
            (fn [name-or-class-a# class-b#]
              (contains? (->> class-b#
                              get-transitive-super-class-and-interface
                              (map #(.. ^SootClass % getName))
                              set)
                         (if (instance? SootClass name-or-class-a#)
                           (.. name-or-class-a# getName)
                           (str name-or-class-a#)))))
           
           soot-init# (fn []
                        ;; set up memoize functions so that they won't retain objects across
                        (alter-var-root #'get-transitive-super-class-and-interface
                                        (fn [_#] get-transitive-super-class-and-interface#))
                        (alter-var-root #'get-interesting-transitive-super-class-and-interface
                                        (fn [_#] get-interesting-transitive-super-class-and-interface#))
                        (alter-var-root #'transitive-ancestor?
                                        (fn [_#] transitive-ancestor?#)))
           
           ;; we have to use this instead of clean# due to the use in ~(when reset? ...)           
           ~'_soot-clean_ (fn []
                            (alter-var-root #'get-transitive-super-class-and-interface
                                            (constantly nil))
                            (alter-var-root #'transitive-ancestor?
                                            (constantly nil))
                            (G/setGlobalObjectGetter nil))]
       (try
         (soot-init#)
         (System/setSecurityManager noexit-security-manager)
         (when (instance? G$GlobalObjectGetter ~g-objgetter)
           (G/setGlobalObjectGetter ~g-objgetter))
         (let [~'soot-g (G/v)
               ~'soot-scene (Scene/v)
               ~'soot-pack-manager (PackManager/v)
               ~'soot-options (Options/v)
               ~'soot-phase-options (PhaseOptions/v)]
           ~@body
           ~(when reset?
              `(~'_soot-clean_)))
         (catch Exception e#
           ;; reset Soot state
           (~'_soot-clean_)
           (throw e#))
         (finally
           (System/setSecurityManager system-security-manager))))))

;;
;; mutter
;;
(def ^:private mutter (java.io.PrintStream. (proxy [java.io.OutputStream] []
                                    (write [_ _1 _2]))))
(def ^:private original-system-out System/out)

(defmacro with-silence
  "execute the body in silence"
  [& body]
  `(try
     (mute)
     ~@body
     (finally
       (unmute))))

(defn mute
  "no output"
  []
  (set! (. (G/v) out) mutter)
  (System/setOut mutter))

(defn unmute
  "allow output again"
  []
  (System/setOut original-system-out)
  (set! (. (G/v) out) original-system-out))
