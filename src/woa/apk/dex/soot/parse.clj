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

(declare parse-apk
         get-apk-interesting-invokes)

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
           soot-result-include-invoke-arguments
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
                                             (->> (get-transitive-super-class-and-interface
                                                   class)
                                                  (filter android-api?)
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
                              (println "descendant" descendant))
                            
                            (swap! result assoc-in
                                   [(.. descendant getPackageName) (.. descendant getName)]
                                   {:android-api-ancestors
                                    (->> (for [super (get-transitive-super-class-and-interface
                                                      descendant)
                                               :when (android-api? super)]
                                           {:class (.. super getName)
                                            :package (.. super getPackageName)})
                                         set)}))
                          ;; cg will only see parts reachable from these entry points
                          (.. soot-scene
                              (setEntryPoints (seq android-api-descendant-callbacks)))
                          ;; return the result
                          {:android-api-descendants android-api-descendants
                           :android-api-descendant-callbacks android-api-descendant-callbacks}))
                
                step1-result (step1)
                
                step2 (fn [{:keys [android-api-descendants
                                   android-api-descendant-callbacks]
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
                            (doseq [callback android-api-descendant-callbacks]
                              (.. pool
                                  (execute
                                   (fn []
                                     (try
                                       (let [callback-class (.. callback getDeclaringClass)]
                                         
                                         (when (and verbose (> verbose 3))
                                           (println "callback" callback))

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
                                                         (map #(if soot-result-include-invoke-arguments
                                                                 (let [{:keys [method args]} %
                                                                       class (-> method get-soot-class)]
                                                                   {:method (-> method get-soot-name)
                                                                    :class (-> method get-soot-class-name)
                                                                    :package (.. class getPackageName)
                                                                    :args (str args)})
                                                                 (let [method %
                                                                       class (-> method get-soot-class)]
                                                                   {:method (-> method get-soot-name)
                                                                    :class (-> method get-soot-class-name)
                                                                    :package (.. class getPackageName)})))
                                                         set)))
                                           ;; add explicit link between invokes and their Android API ancestor
                                           (let [path [(.. callback-class getPackageName)
                                                       (.. callback-class getName)
                                                       :callbacks
                                                       (.. callback getName)
                                                       :descend]]
                                             (doseq [invoke (set/union explicit-invokes implicit-invokes)]
                                               (let [method (if soot-result-include-invoke-arguments
                                                              (:method invoke)
                                                              invoke)]
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
                                                                #(conj (set %1) %2) v))))))))
                                           ))
                                       (catch Exception e
                                         (print-stack-trace-if-verbose e verbose)))))))
                            (.. pool shutdown)
                            (try
                              (when-not (.. pool (awaitTermination Integer/MAX_VALUE
                                                                   TimeUnit/SECONDS))
                                (.. pool shutdownNow))
                              (catch InterruptedException e
                                (.. pool shutdownNow)
                                (.. Thread currentThread interrupt))))
                          
                          ;; must be in Soot body to ensure content/arguments can be printed
                          (when (or soot-show-result
                                    (and verbose (> verbose 2)))
                            (pprint @result))))
                step2-result (step2 step1-result)])
          ;; catch Exception to prevent disrupting outer threads
          (catch Exception e
            (print-stack-trace-if-verbose e verbose))
          (finally
            (unmute))))
      @result)))
