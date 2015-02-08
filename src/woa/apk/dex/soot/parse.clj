(ns woa.apk.dex.soot.parse
  ;; internal libs
  (:require [woa.util
             :refer [print-stack-trace-if-verbose]])
  (:require [woa.apk.dex.soot.util
             :as util
             :refer :all])
  (:require [woa.apk.dex.soot.simulator
             :as simulator
             :refer :all])  
  (:require [woa.apk.parse
             :as apk-parse])
  
  ;; common libs
  (:require [clojure.string :as str]
            [clojure.set :as set]
            [clojure.walk :as walk]
            [clojure.zip :as zip]
            [clojure.java.io :as io]
            [clojure.pprint :refer [pprint print-table]]
            [clojure.stacktrace :refer [print-stack-trace]])  
  ;; special lib
  (:require [me.raynes.fs :as fs])  
  ;; imports
  (:import (java.util.concurrent Executors
                                 TimeUnit))
  (:import (soot Unit
                 SootField
                 SootClass
                 SootMethod
                 SootMethodRef)
           (soot.jimple Stmt)
           (soot.options Options)))

;;; declaration

;; func

;; public
(declare parse-apk get-apk-interesting-invokes)

;; private
(declare prettify-args)

;;; implementation

(defn parse-apk
  "parse apk with soot"
  [apk-name options]
  (merge (apk-parse/parse-apk apk-name)
         {:dex (get-apk-interesting-invokes apk-name {}
                                            options)}))

(defn get-apk-interesting-invokes
  "get App components and their (transitive) interesting invokes"
  [apk-name
   {:keys [exclusion-name-patterns
           exclusion-name-pattern-exceptions]
    :as params
    :or {exclusion-name-patterns [#"^java\."
                                  #"^javax\."
                                  #"^junit\."
                                  #"^org\.json"
                                  #"^org\.w3c\."
                                  #"^org\.xmlpull\."]
         exclusion-name-pattern-exceptions [#"^android\."
                                            #"^com\.android\."
                                            #"^dalvik\."
                                            #"^java\.lang\.System"
                                            #"^java\.lang\.Class"
                                            #"^java\.lang\.ClassLoader"
                                            #"^java\.lang\.reflect"
                                            #"^java\.security"]}}
   {:keys [soot-android-jar-path
           soot-show-result
           soot-result-exclude-app-methods
           soot-parallel-jobs
           verbose]
    :as options}]
  (when (and apk-name (fs/readable? apk-name))
    (let [apk-path (.getPath (io/file apk-name))
          get-android-jar-path #(let [res-name "EMPTY"
                                      ;; hack to get "woa.jar" dir
                                      [_ path] (re-find (re-pattern (str "^file:(.*)/[^/]+!/"
                                                                         res-name "$"))
                                                        (.getPath (io/resource res-name)))]
                                  (str/join (System/getProperty "file.separator")
                                            [path "android.jar"]))
          android-jar-path (if soot-android-jar-path
                             soot-android-jar-path
                             (get-android-jar-path))
          result (atom {})
          ;; the current thread's Soot context
          g-objgetter (new-g-objgetter)]
      ;; unfortunately, Singleton is so deeply embedded in Soot's implementation, we have to work in critical Section altogether
      (with-soot
        ;; use the current thread's Soot context
        g-objgetter
        ;; reset at the end to release the Soot Objects built up during the analysis
        true
        ;; the real work begins from here
        (when (or (not verbose)
                  (<= verbose 1))
          (mute))
        (try
          (doto soot-options
            (.set_src_prec (Options/src_prec_apk))
            (.set_process_dir [apk-path])
            (.set_force_android_jar android-jar-path)
            
            (.set_allow_phantom_refs true)
            (.set_no_bodies_for_excluded true)
            (.set_ignore_resolution_errors true)
            
            (.set_whole_program true)
            (.set_output_format (Options/output_format_none)))
          (doto soot-phase-options)
          ;; do it manually --- barebone
          (run-body-packs :scene soot-scene
                          :pack-manager soot-pack-manager
                          :body-packs ["jb"]
                          :verbose verbose)
          
          (when (and verbose (> verbose 3))
            (println "body pack finished"))
          
          ;; start working on the bodies
          (let [step1 (fn []
                        (let [application-classes (get-application-classes soot-scene)
                              
                              android-api-descendants
                              (->> application-classes
                                   (filter (fn [class]
                                             (->> (get-interesting-transitive-super-class-and-interface
                                                   class android-api?)
                                                  not-empty))))
                              
                              android-api-descendant-callbacks
                              (->> android-api-descendants
                                   (remove #(.. ^SootClass % isPhantom))
                                   (mapcat #(->> (.. ^SootClass % getMethods)
                                                 (filter (fn [method]
                                                           (and (.hasActiveBody method)
                                                                (re-find #"^on[A-Z]"
                                                                         (.getName method)))))))
                                   set)]
                          ;; descendant relations
                          (doseq [descendant android-api-descendants]
                            
                            (when (and verbose (> verbose 3))
                              (println "android API descendants:" descendant))
                            
                            (swap! result assoc-in
                                   [(.. descendant getPackageName) (.. descendant getName)]
                                   {:android-api-ancestors
                                    (->> (for [super (get-interesting-transitive-super-class-and-interface
                                                      descendant android-api?)]
                                           {:class (.. super getName)
                                            :package (.. super getPackageName)})
                                         set)}))
                          ;; cg will only see parts reachable from these entry points
                          (.. soot-scene
                              (setEntryPoints (seq android-api-descendant-callbacks)))
                          ;; return the result
                          {:android-api-descendants android-api-descendants}))
                
                step1-result (step1)
                
                step2 (fn [{:keys [android-api-descendants]
                            :as prev-step-result}]
                        (let [application-classes (get-application-classes soot-scene)
                              application-methods (get-application-methods soot-scene)

                              interesting-method?
                              (memoize
                               (fn [method]
                                 (let [method-name (-> method get-soot-name)
                                       class (-> method get-soot-class)
                                       ;;super (-> class get-transitive-super-class-and-interface)
                                       ]
                                   ;; interestingness criteria
                                   (and true
                                        (if soot-result-exclude-app-methods
                                          ;; external
                                          (not (contains? application-methods method))
                                          true)
                                        ;; not in exclusion-name-patterns
                                        (or (->> [class]
                                                 (filter
                                                  (fn [x]
                                                    (some #(re-find % (-> x get-soot-class-name))
                                                          exclusion-name-patterns)))
                                                 empty?)
                                            ;; ... unless in exclusion-name-pattern-exceptions
                                            (->> [class]
                                                 (filter
                                                  (fn [x]
                                                    (some #(re-find % (-> x get-soot-class-name))
                                                          exclusion-name-pattern-exceptions)))
                                                 not-empty))
                                        ;; not <init> or <clinit>
                                        (not (re-find #"<[^>]+>" method-name))))))]

                          (let [pool (Executors/newFixedThreadPool soot-parallel-jobs)]
                            (doseq [descendant android-api-descendants]
                              (.. pool
                                  (execute
                                   (fn []
                                     ;; impose lifecycle order on callbacks: https://developer.android.com/images/activity_lifecycle.png
                                     (let [callbacks
                                           (->> (.. ^SootClass descendant getMethods)
                                                (filter (fn [method]
                                                          (and (.hasActiveBody method)
                                                               (re-find #"^on[A-Z]"
                                                                        (.getName method)))))
                                                (sort-by #(.getName %)
                                                         (fn [x y]
                                                           (let [order {"onCreate" 1
                                                                        "onStart" 2
                                                                        "onResume" 3
                                                                        "onPause" 4
                                                                        "onStop" 5
                                                                        "onRestart" 6
                                                                        "onDestroy" 7}
                                                                 ox (get order x)
                                                                 oy (get order y)]
                                                             (cond
                                                               (and (number? ox)
                                                                    (number? oy))
                                                               (compare ox oy)

                                                               (nil? oy)
                                                               -1

                                                               (nil? ox)
                                                               1)))))]
                                       (try
                                         (doseq [callback callbacks]
                                           (let [callback-class (.. callback getDeclaringClass)]
                                             
                                             (when (and verbose (> verbose 3))
                                               (println "app component callback:" callback))

                                             (let [{:keys [explicit-invokes
                                                           implicit-invokes
                                                           component-invokes]}
                                                   (with-simulator
                                                     (initialize-classes {:classes application-classes
                                                                          :circumscription application-methods}
                                                                         options)                                                 
                                                     (get-all-interesting-invokes callback
                                                                                  interesting-method?
                                                                                  application-methods
                                                                                  options))]
                                               (doseq [[type invokes] [[:explicit explicit-invokes]
                                                                       [:implicit implicit-invokes]
                                                                       [:component component-invokes]]]
                                                 (swap! result assoc-in
                                                        [(.. callback-class getPackageName)
                                                         (.. callback-class getName)
                                                         :callbacks
                                                         (.. callback getName)
                                                         type]
                                                        (->> invokes
                                                             (filter #(let [{:keys [method args]} %]
                                                                        (soot-queryable? method)))
                                                             (map #(let [{:keys [method args]} %
                                                                         class (-> method
                                                                                   get-soot-class)]
                                                                     {:method (-> method get-soot-name)
                                                                      :class (-> method get-soot-class-name)
                                                                      :package (.. class getPackageName)
                                                                      :args (->> args prettify-args str)}))
                                                             set)))
                                               ;; add explicit link between invokes and their Android API ancestor
                                               (let [path [(.. callback-class getPackageName)
                                                           (.. callback-class getName)
                                                           :callbacks
                                                           (.. callback getName)
                                                           :descend]]
                                                 (doseq [invoke (set/union explicit-invokes implicit-invokes)]
                                                   (let [method (:method invoke)]
                                                     (when (soot-queryable? method)
                                                       (when-not (android-api? method)
                                                         (let [method-name (-> method get-soot-name)
                                                               method-class (-> method get-soot-class)
                                                               v {:method method-name
                                                                  :class (-> method get-soot-class-name)
                                                                  :package (.. method-class getPackageName)}
                                                               ;; Android API supers
                                                               supers (->> method-class
                                                                           get-transitive-super-class-and-interface
                                                                           (filter android-api?))]
                                                           (when-let [super (some #(try
                                                                                     (if (.. ^soot.SootClass %
                                                                                             (getMethodByNameUnsafe
                                                                                              method-name))
                                                                                       %
                                                                                       false)
                                                                                     ;; Soot implementation: Ambiguious 
                                                                                     (catch RuntimeException e
                                                                                       %))
                                                                                  supers)]
                                                             (let [k {:method method-name
                                                                      :class (-> super get-soot-class-name)
                                                                      :package (.. super getPackageName)}]
                                                               (swap! result update-in (conj path k)
                                                                      #(conj (set %1) %2) v))))))))))))
                                         (catch Exception e
                                           (print-stack-trace-if-verbose e verbose))))))))
                            (.. pool shutdown)
                            (try
                              (when-not (.. pool (awaitTermination Integer/MAX_VALUE
                                                                   TimeUnit/SECONDS))
                                (.. pool shutdownNow))
                              (catch InterruptedException e
                                (.. pool shutdownNow)
                                (.. Thread currentThread interrupt))))
                          
                          ;; must be in Soot body to ensure content/arguments can be printed
                          (when soot-show-result
                            (pprint @result))))
                step2-result (step2 step1-result)])
          ;; catch Exception to prevent disrupting outer threads
          (catch Exception e
            (print-stack-trace-if-verbose e verbose))
          (finally
            (unmute))))
      @result)))

(defn- prettify-args
  "prettify results"
  [args]
  (try
    (cond
      (instance? woa.apk.dex.soot.sexp.ErrorSexp args)
      (list (prettify-args (:type args)) (prettify-args (:info args)))
      
      (instance? woa.apk.dex.soot.sexp.ExternalSexp args)
      (list :instance (prettify-args (:type args)))

      (or (instance? woa.apk.dex.soot.sexp.BinaryOperationSexp args)
          (instance? woa.apk.dex.soot.sexp.UnaryOperationSexp args))
      (list* (:operator args)
             (map prettify-args (:operands args)))

      (instance? woa.apk.dex.soot.sexp.InvokeSexp args)
      (list :invoke
            (prettify-args (:method args))
            (prettify-args (:base args))
            (prettify-args (:args args)))
      
      (instance? woa.apk.dex.soot.sexp.InstanceSexp args)
      (list :instance (prettify-args (:instance args)))
      
      (instance? woa.apk.dex.soot.sexp.MethodSexp args)
      (list :method (prettify-args (:method args)))

      (instance? woa.apk.dex.soot.sexp.FieldSexp args)
      (list :field (prettify-args (:field args)))

      (instance? woa.apk.dex.soot.sexp.InstanceOfSexp args)
      (list :instance-of
            (prettify-args (:class args))
            (prettify-args (:instance args)))

      (instance? woa.apk.dex.soot.sexp.NewArraySexp args)
      (list :new-array
            (prettify-args (:base-type args))
            (prettify-args (:size args)))

      (instance? woa.apk.dex.soot.sexp.NewMultiArraySexp args)
      (list :new-multi-array
            (prettify-args (:base-type args))
            (prettify-args (:sizes args)))

      (instance? woa.apk.dex.soot.sexp.ArrayRefSexp args)
      (list :array-ref
            (prettify-args (:base args))
            (prettify-args (:index args)))

      (instance? woa.apk.dex.soot.sexp.ConstantSexp args)
      (list :constant
            (prettify-args (:const args)))

      (or (instance? soot.SootClass args))
      (list :class (get-soot-name args))

      (or (instance? soot.SootMethod args)
          (instance? soot.SootMethodRef args))
      (list :method (str (get-soot-class-name args)
                         "."
                         (get-soot-name args)))

      (or (instance? soot.SootField args)
          (instance? soot.SootMethodRef args))
      (list :field (str (get-soot-class-name args)
                        "."
                        (get-soot-name args)))
      
      (soot-queryable? args)
      (->> args get-soot-name)

      (and (not (instance? woa.apk.dex.soot.sexp.Sexp args))
           (coll? args))
      (->> args
           (map prettify-args)
           (into (empty args)))    
      
      :otherwise
      args)
    (catch Exception e
      args)))
