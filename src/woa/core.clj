(ns woa.core
  ;; internal libs
  (:require [woa.util
             :refer [print-stack-trace-if-verbose]]
            [woa.core.signature
             :refer [compute-cgdfd-signature
                     compute-cgdfd]]
            [woa.apk.parse
             :as apk-parse]
            [woa.apk.aapt.parse
             :as aapt-parse]
            [woa.neo4j.core
             :as neo4j]
            [woa.apk.dex.soot.parse
             :as soot-parse]
            [woa.virustotal.core
             :as vt]
            )
  ;; common libs
  (:require [clojure.string :as str]
            [clojure.set :as set]
            [clojure.walk :as walk]
            [clojure.zip :as zip]
            [clojure.java.io :as io]
            [clojure.pprint :refer [pprint print-table]]
            [clojure.stacktrace :refer [print-stack-trace]])
  ;; special libs
  (:require [clojure.tools.cli :refer [parse-opts]])
  (:require [clojure.java.shell :refer [sh]])
  (:require [me.raynes.fs :as fs])
  (:require [clojure.tools.nrepl.server :refer [start-server stop-server]])
  (:require [cider.nrepl :refer [cider-nrepl-handler]])
  (:require [taoensso.nippy :as nippy])
  ;; imports
  (:import (java.util.concurrent Executors
                                 TimeUnit))
  ;; config
  (:gen-class))

(def cli-options
  [
   ;; general options
   ["-h" "--help" "you are reading it now"]
   ["-v" "--verbose" "be verbose (more \"v\" for more verbosity)"
    :default 0
    :assoc-fn (fn [m k _] (update-in m [k] inc))]
   ["-L" "--no-line-reading" "do not read from stdin; exit if other tasks complete"]
   
   ["-i" "--interactive" "do not exit (i.e., shutdown-agents) at the end"]
   [nil "--delay-start SEC" "delay start for a random seconds from 1 to (max) SEC"
    :parse-fn #(Integer/parseInt %)
    :default 0]

   ;; nREPL config
   [nil "--nrepl-port PORT" "REPL port"
    :parse-fn #(Integer/parseInt %)
    :validate [#(< 0 % 0x10000)
               (format "Must be a number between 0 and %d (exclusively)"
                       0x10000)]]
   
   ;; prepations
   [nil "--prep-tags TAGS" "TAGS is a Clojure vector of pairs of label types to properties, e.g., [[[\"Dataset\"] {\"id\" \"dataset-my\" \"name\" \"my dataset\"}]]"]
   [nil "--prep-virustotal" "obtain VirusTotal tags"]
   [nil "--virustotal-apikey APIKEY" "VirusTotal API key"]
   [nil "--virustotal-rate-limit LIMIT-PER-MIN" "number of maximal API calls per minute"
    :parse-fn #(Integer/parseInt %)
    :default 4]
   [nil "--virustotal-backoff SEC" "number of seconds to backoff when exceeding rate limit"
    :parse-fn #(Integer/parseInt %)
    :default 5]   
   [nil "--virustotal-submit" "whether submit sample to VirusTotal if not found"]
   
   ;; Soot config
   ["-s" "--soot-task-build-model" "build APK model with Soot"]
   [nil "--soot-android-jar-path PATH" "path of android.jar for Soot's Dexpler"]
   [nil "--soot-basic-block-simulation-budget BUDGET" "basic block simulation budget"
    :parse-fn #(Long/parseLong %)
    :default 50]
   [nil "--soot-method-simulation-depth-budget BUDGET" "method invocation simulation budget"
    :parse-fn #(Long/parseLong %)
    :default 10]
   [nil "--soot-simulation-collection-size-budget BUDGET" "array size simulation budget"
    :parse-fn #(Long/parseLong %)
    :default 10000]   
   [nil "--soot-simulation-conservative-branching" "branching based on conditions: more precision at the cost of less coverage before budget depletion."]
   [nil "--soot-simulation-linear-scan" "do not branch or loop: more coverage at the cost of precision"]   
   ["-j" "--soot-parallel-jobs JOBS"
    "number of concurrent threads for analyzing methods"
    :parse-fn #(Integer/parseInt %)
    :default 1
    :validate [#(> % 0)
               (format "You need at least 1 job to proceed")]]
   [nil "--soot-show-result" "show APK analysis result"]
   
   [nil "--soot-no-implicit-cf" "do not detect implicit control flows (for comparison)"]
   [nil "--soot-dump-all-invokes" "dump all invokes"]
   [nil "--soot-result-exclude-app-methods" "exclude app internal methods from the result"]

   [nil "--soot-debug-show-each-statement" "debug facility: show each processed statement"]
   [nil "--soot-debug-show-locals-per-statement" "debug facility: show locals per each statement"]
   [nil "--soot-debug-show-all-per-statement" "debug facility: show all per each statement"]
   [nil "--soot-debug-show-implicit-cf" "debug facility: show all implicit control flows"]
   [nil "--soot-debug-show-safe-invokes" "debug facility: show all safe invokes"]
   [nil "--soot-debug-show-exceptions" "debug facility: show all exceptions"]   
   
   ["-d" "--dump-model FILE" "dump binary APK model; append dump file paths to FILE"]
   ["-O" "--overwrite-model" "overwrite model while dumping"]   
   ["-l" "--load-model FILE" "load binary APK model; load from dump file paths in FILE"]
   ["-c" "--convert-model" "convert model between binary and readable formats"]
   [nil "--readable-model" "dump/load readable APK model; --dump/load-model FILE will dump/load readable model directly to/from FILE"]
   [nil "--println-model" "println loaded APK model"]
   [nil "--pprint-model" "pprint loaded APK model"]

   ;; Neo4j config
   [nil "--neo4j-port PORT" "Neo4j server port"
    :parse-fn #(Integer/parseInt %)
    :default 7474
    :validate [#(< 0 % 0x10000)
               (format "Must be a number between 0 and %d (exclusively)"
                       0x10000)]]
   [nil "--neo4j-protocol PROTOCOL" "Neo4j server protocol (http/https)"
    :default "http"]
   [nil "--neo4j-conn-backoff SEC" "Neo4j connection retry max random backoff in seconds"
    :parse-fn #(Integer/parseInt %)
    :default 60]
   
   ;; Neo4j tasks
   ["-n" "--neo4j-task-populate" "populate Neo4j with APK model"]
   ["-t" "--neo4j-task-tag" "tag Neo4j Apk nodes with labels"]
   ["-T" "--neo4j-task-untag" "untag Neo4j Apk nodes with labels"]
   ["-g" "--neo4j-task-add-callback-signature" "add Neo4j CallbackSignature nodes"]
   ["-G" "--neo4j-task-remove-callback-signature" "remove Neo4j CallbackSignature nodes"]   
   [nil "--neo4j-include-methodinstance" "include MethodInstance in the WoA model"]
   [nil "--neo4j-no-callgraph" "not include call graph (CG) in the WoA model"]   
   ["-D" "--neo4j-dump-model-batch-csv PREFIX" "dump Neo4j batch import CSV files to PREFIX; ref: https://github.com/jexp/batch-import/tree/2.1"]
   
   ;; misc tasks
   [nil "--dump-manifest" "dump AndroidManifest.xml"]

   ])

(def main-options
  "for consumption by nREPL session"
  (atom nil))

(def mutex
  "establish critical section"
  (Object.))

(def completed-task-counter
  "completed task counter"
  (atom 0))

(defmacro with-mutex-locked
  "synchronize verbose ouput"
  [& body]
  `(locking mutex
     ~@body))

(defn work
  "do the real work on apk"
  [{:keys [file-path tags]
    :as task}
   {:keys [verbose
           soot-task-build-model
           dump-model overwrite-model readable-model
           neo4j-port neo4j-protocol
           neo4j-task-populate neo4j-task-tag neo4j-task-untag
           neo4j-task-add-callback-signature neo4j-task-remove-callback-signature
           dump-manifest]
    :as options}]
  (when (and file-path (fs/readable? file-path))
    (when (and verbose (> verbose 1))
      (println "processing" file-path))
    
    (let [start-time (System/currentTimeMillis)]
      (try
        (when dump-manifest
          (print (aapt-parse/get-manifest-xml file-path))
          (flush))

        (when soot-task-build-model
          (let [apk (apk-parse/parse-apk file-path)
                dump-fname (str (:sha256 apk) ".model-dump")]
            (when (or overwrite-model
                      (not (and dump-model (fs/exists? dump-fname)
                                (do
                                  (when verbose
                                    (println dump-fname
                                             "exists: skipped;"
                                             "overwrite with \"--overwrite-model\""))
                                  true))))
              (let [apk (soot-parse/parse-apk file-path
                                              (merge options
                                                     ;; piggyback layout-callbacks on options
                                                     {:layout-callbacks
                                                      (aapt-parse/get-layout-callbacks file-path)}))]
                (when dump-model
                  (try
                    (with-open [model-io (io/writer dump-model :append true)]
                      (binding [*out* model-io]
                        (if readable-model
                          (prn apk)
                          (with-open [model-io (io/output-stream dump-fname)]
                            (nippy/freeze-to-out! (java.io.DataOutputStream. model-io)
                                                  apk)
                            ;; write the dump file name out
                            (println dump-fname)))))
                    (catch Exception e
                      (print-stack-trace-if-verbose e verbose))))
                
                (when neo4j-task-populate
                  (neo4j/populate-from-parsed-apk apk
                                                  options))
                
                (cond
                  neo4j-task-add-callback-signature
                  (try
                    (neo4j/add-callback-signature apk
                                                  options)
                    (catch Exception e
                      (print-stack-trace-if-verbose e verbose)))

                  neo4j-task-remove-callback-signature
                  (try
                    (neo4j/remove-callback-signature apk
                                                     options)
                    (catch Exception e
                      (print-stack-trace-if-verbose e verbose))))))))
        
        (let [apk (apk-parse/parse-apk file-path)]
          (cond
            neo4j-task-tag (neo4j/tag-apk apk tags options)
            neo4j-task-untag (neo4j/untag-apk apk tags options)))        
        
        (when (and verbose (> verbose 0))
          (with-mutex-locked
            (swap! completed-task-counter inc)
            (println (format "%1$d: %2$s processed in %3$.3f seconds"
                             @completed-task-counter
                             file-path
                             (/ (- (System/currentTimeMillis) start-time)
                                1000.0)))))
        
        (catch Exception e
          (print-stack-trace-if-verbose e verbose))))))

(defn -main
  "main entry"
  [& args]
  (let [raw (parse-opts args cli-options)
        {:keys [options summary errors]} raw
        {:keys [verbose interactive delay-start help no-line-reading
                prep-tags
                prep-virustotal
                virustotal-rate-limit virustotal-backoff virustotal-submit
                nrepl-port
                load-model dump-model convert-model println-model pprint-model
                readable-model
                neo4j-task-populate
                neo4j-task-add-callback-signature neo4j-task-remove-callback-signature
                neo4j-dump-model-batch-csv]} options]
    (try
      ;; print out error messages if any
      (when errors
        (binding [*out* *err*]
          (doseq [error errors]
            (println error))))
      ;; whether help is requested
      (cond
        help
        (do
          (println "<BUILDINFO>")
          (println summary))

        (or prep-tags prep-virustotal)
        (do
          ;; for API rate limit
          (let [vt-api-call-counter (atom virustotal-rate-limit)
                vt-start-time (atom (System/currentTimeMillis))]
            (loop [line (read-line)]
              (when line
                (try
                  (prn (-> {:file-path line :tags []}
                           
                           
                           (update-in [:tags] into
                                      (when (and prep-tags
                                                 (not (str/blank? prep-tags)))
                                        (read-string prep-tags)))
                           
                           
                           (update-in [:tags] into
                                      (when prep-virustotal
                                        (let [apk (apk-parse/parse-apk line)
                                              
                                              try-backoff
                                              (fn []
                                                (when (<= @vt-api-call-counter 0)
                                                  (let [now (System/currentTimeMillis)
                                                        
                                                        sleep-time
                                                        (max (* virustotal-backoff 1000)
                                                             (- (+ @vt-start-time
                                                                   (* 60 1000))
                                                                now))]
                                                    (reset! vt-api-call-counter
                                                            virustotal-rate-limit)
                                                    (reset! vt-start-time
                                                            now)
                                                    (Thread/sleep sleep-time))))]
                                          (when-let [sha256 (:sha256 apk)]
                                            (try-backoff)
                                            (when-let [result (vt/get-report {:sha256 sha256}
                                                                             options)]
                                              (swap! vt-api-call-counter dec)
                                              (when (and verbose (> verbose 2))
                                                (binding [*out* *err*]
                                                  (println "virustotal report" result)))
                                              (let [ret (atom nil)]
                                                (cond
                                                  ;; if result is a map, the result is returned
                                                  (map? result)
                                                  (reset! ret
                                                          (vt/make-report-result-into-tags result))
                                                  
                                                  (= result :status-exceed-api-limit)
                                                  (try-backoff)

                                                  (= result :response-not-found)
                                                  (when virustotal-submit
                                                    (try-backoff)
                                                    (let [result
                                                          (vt/submit-file {:file-content (io/file line)}
                                                                          options)]
                                                      (when (and verbose (> verbose 2))
                                                        (binding [*out* *err*]
                                                          (println "virustotal submit" result))))
                                                    (swap! vt-api-call-counter dec)))
                                                @ret))))))))
                  (catch Exception e
                    (print-stack-trace-if-verbose e verbose)))
                (recur (read-line))))))

        :otherwise
        (do
          (when (and delay-start
                     (> delay-start 0))
            (let [delay-start (rand-int delay-start)]
              (when (> verbose 1)
                (println "delay start" delay-start "seconds"))
              (Thread/sleep (* delay-start 1000))))
          (when nrepl-port
            ;; use separate thread to start nREPL, so do not delay other task
            (.. (Thread.
                 (fn []
                   (try
                     (start-server :port nrepl-port
                                   :handler cider-nrepl-handler)
                     (catch Exception e
                       (when (> verbose 1)
                         (binding [*out* *err*]
                           (println "error: nREPL server cannot start at port"
                                    nrepl-port)))))))
                start))

          (when neo4j-task-populate
            ;; "create index" only need to executed once if populate-neo4j is requested
            (when (> verbose 1)
              (with-mutex-locked
                (println "Neo4j:" "creating index")))
            (neo4j/create-index options)
            (when (> verbose 1)
              (with-mutex-locked
                (println "Neo4j:" "index created"))))

          ;; load Soot model and populate Neo4j graph
          ;; single-threaded to avoid Neo4j contention
          (when load-model
            (try
              (let [counter (atom 0)]
                (with-open [model-io (io/reader load-model)]
                  (binding [*in* model-io]
                    (loop [line (read-line)]
                      (when line
                        (let [apk (try
                                    (if readable-model
                                      (read-string line)
                                      (with-open [model-io (io/input-stream line)]
                                        (nippy/thaw-from-in! (java.io.DataInputStream. model-io))))
                                    (catch Exception e
                                      (print-stack-trace-if-verbose e verbose)
                                      nil))]
                          (when apk

                            (when neo4j-dump-model-batch-csv
                              (neo4j/add-to-batch-csv apk options))
                            
                            (when (and apk convert-model dump-model)
                              (try
                                (with-open [model-io (io/writer dump-model :append true)]
                                  (binding [*out* model-io]
                                    (if readable-model ; if --load-model is in readable format
                                      ;; convert to binary model
                                      (let [dump-fname (str (:sha256 apk) ".model-dump")]
                                        (with-open [model-io (io/output-stream dump-fname)]
                                          (nippy/freeze-to-out! (java.io.DataOutputStream. model-io)
                                                                apk)
                                          ;; write the dump file name out
                                          (println dump-fname)))
                                      ;; convert to readable model
                                      (prn apk))))
                                (catch Exception e
                                  (print-stack-trace-if-verbose e verbose))))
                            
                            ((cond pprint-model pprint
                                   println-model println
                                   ;; nop
                                   :otherwise (constantly nil)) apk)

                            (swap! counter inc)
                            (when (and verbose
                                       (> verbose 0))
                              (println (format "%1$d:" @counter)
                                       (get-in apk [:manifest :package])
                                       (get-in apk [:manifest :android:versionCode])
                                       (get-in apk [:sha256])))
                            (when neo4j-task-populate
                              (try
                                (neo4j/populate-from-parsed-apk apk
                                                                options)
                                (catch Exception e
                                  (print-stack-trace-if-verbose e verbose))))

                            (cond
                              neo4j-task-add-callback-signature
                              (try
                                (neo4j/add-callback-signature apk
                                                              options)
                                (catch Exception e
                                  (print-stack-trace-if-verbose e verbose)))

                              neo4j-task-remove-callback-signature
                              (try
                                (neo4j/remove-callback-signature apk
                                                                 options)
                                (catch Exception e
                                  (print-stack-trace-if-verbose e verbose)))))
                          (recur (read-line))))))))
              (when neo4j-dump-model-batch-csv
                (neo4j/dump-batch-csv neo4j-dump-model-batch-csv options))
              (catch Exception e
                (print-stack-trace-if-verbose e verbose))))

          ;; do the work for each line
          (when-not no-line-reading
            (loop [line (read-line)]
              (when line
                ;; ex.: {:file-path "a/b.apk" :tags [{["Dataset"] {"id" "dst-my" "name" "my dataset"}}]}
                ;; tags must have "id" node property
                (let [{:keys [file-path tags] :as task}
                      (try
                        (read-string line)
                        (catch Exception e
                          (print-stack-trace-if-verbose e verbose)
                          nil))]
                  (try
                    (when (and file-path (fs/readable? file-path))
                      (work task options))
                    (catch Exception e
                      (print-stack-trace-if-verbose e verbose)))
                  (recur (read-line))))))
          
          (when neo4j-task-populate
            (when (> verbose 1)
              (with-mutex-locked
                (println "Neo4j:" "marking Android API")))
            ;; mark Android API
            (neo4j/mark-android-api options)
            (when (> verbose 1)
              (with-mutex-locked
                (println "Neo4j:" "Android API marked")))))) 
      (when interactive
        ;; block when interactive is requested
        @(promise))
      (catch Exception e
        (print-stack-trace-if-verbose e verbose))
      (finally
        ;; clean-up
        (shutdown-agents)    
        (when (> verbose 1)
          (with-mutex-locked
            (println "shutting down")))
        (System/exit 0)))))
