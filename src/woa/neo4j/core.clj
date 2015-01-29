(ns woa.neo4j.core
  ;; internal libs
  (:require [woa.util
             :refer [print-stack-trace-if-verbose]])  
  ;; common libs
  (:require [clojure.string :as str]
            [clojure.set :as set]
            [clojure.walk :as walk]
            [clojure.zip :as zip]
            [clojure.java.io :as io]
            [clojure.pprint :refer [pprint print-table]]
            [clojure.stacktrace :refer [print-stack-trace]])
  ;; special libs
  (:require [clojurewerkz.neocons.rest :as nr]
            [clojurewerkz.neocons.rest.transaction :as ntx]))

(declare populate-from-parsed-apk 
         tag-apk untag-apk
         create-index mark-android-api
         connect android-api?)

(def defaults (atom {:neo4j-port 7474
                     :neo4j-protocol "http"}))

(defn populate-from-parsed-apk
  "populate the database with the parsed apk structure"
  [apk {:keys []
        :as options}]
  (let [manifest (:manifest apk)
        dex-sha256 (:dex-sha256 apk)
        cert-sha256 (:cert-sha256 apk)
        apk-sha256 (:sha256 apk)
        apk-package (:package manifest)
        apk-version-name (:android:versionName manifest)
        apk-version-code (:android:versionCode manifest)
        dex (:dex apk)
        conn (connect options)
        transaction (ntx/begin-tx conn)]
    (ntx/with-transaction
      conn
      transaction
      true

      ;; do not stack up the query strings for memory efficiency: execute as soon as possible

      ;; overall structure
      (ntx/execute
       conn transaction
       [(ntx/statement
         (str/join " "
                   ["MERGE (signkey:SigningKey {sha256:{certsha256}})"
                    "MERGE (apk:Apk {sha256:{apksha256},package:{apkpackage},versionCode:{apkversioncode},versionName:{apkversionname}})"
                    "MERGE (dex:Dex {sha256:{dexsha256}})"
                    "MERGE (signkey)-[:SIGN]->(apk)-[:CONTAIN]->(dex)"
                    "FOREACH ("
                    "perm in {usespermission} |"
                    "  MERGE (n:Permission {name:perm})"
                    "  MERGE (n)<-[:USE]-(apk)"
                    ")"
                    "FOREACH ("
                    "perm in {permission} |"
                    "  MERGE (n:Permission {name:perm})"
                    "  MERGE (n)<-[:DEFINE]-(apk)"
                    ")"])
         {:certsha256 cert-sha256
          :apksha256 apk-sha256
          :dexsha256 dex-sha256
          :usespermission (->> manifest
                               :uses-permission
                               (map name)
                               ;; only consider Android internal API ones
                               ;;(filter android-api?)
                               )
          :permission (->> manifest
                           :permission
                           (map name)
                           ;; only consider API ones
                           ;;(filter android-api?)
                           )
          :apkpackage apk-package
          :apkversionname apk-version-name
          :apkversioncode apk-version-code})])
      
      (doseq [package-name (->> dex keys)]
        (doseq [class-name (->> (get-in dex [package-name]) keys)]
          (ntx/execute
           conn transaction
           [(ntx/statement
             (str/join " "
                       ["MERGE (dex:Dex {sha256:{dexsha256}})"
                        "MERGE (package:Package {name:{packagename}})"
                        "MERGE (class:Class {name:{classname}})"
                        "MERGE (package)-[:CONTAIN]->(class)"
                        "MERGE (dex)-[:CONTAIN]->(class)"])
             {:dexsha256 dex-sha256
              :packagename package-name
              :classname class-name})])
          
          (let [{:keys [android-api-ancestors callbacks]} (->> (get-in dex [package-name class-name]))]
            (doseq [base android-api-ancestors]
              (let [ancestor-package (:package base)
                    ancestor-class (:class base)]
                (ntx/execute
                 conn transaction
                 [(ntx/statement
                   (str/join " "
                             ["MERGE (class:Class {name:{classname}})"
                              "MERGE (ancestorpackage:AndroidAPI:Package {name:{ancestorpackage}})"
                              "MERGE (ancestorclass:AndroidAPI:Class {name:{ancestorclass}})"
                              "MERGE (ancestorpackage)-[:CONTAIN]->(ancestorclass)"
                              "MERGE (class)-[:DESCEND]->(ancestorclass)"])
                   {:classname class-name
                    :ancestorpackage ancestor-package
                    :ancestorclass ancestor-class})])))
            (doseq [callback-name (->> callbacks keys)]
              (let [path [package-name class-name :callbacks callback-name]]
                (ntx/execute
                 conn transaction
                 [(ntx/statement
                   (str/join " "
                             ["MERGE (class:Class {name:{classname}})"
                              "MERGE (callback:Method:Callback {name:{callbackname}})"
                              "MERGE (class)-[:CONTAIN]->(callback)"])
                   {:classname class-name
                    :callbackname (str class-name "." callback-name)})])
                ;; explicit control flow
                (let [path (conj path :explicit)]
                  (doseq [callback-invoke (get-in dex path)]
                    (let [invoke-package-name (:package callback-invoke)
                          invoke-class-name (:class callback-invoke)
                          invoke-name (:method callback-invoke)
                          args (:args callback-invoke)]
                      (ntx/execute
                       conn transaction
                       [(ntx/statement
                         (str/join " "
                                   ["MERGE (callback:Method:Callback {name:{callbackname}})"
                                    "MERGE (invokepackage:Package {name:{invokepackagename}})"
                                    "MERGE (invokeclass:Class {name:{invokeclassname}})"
                                    (if args
                                      "MERGE (invokename:Method {name:{invokename},args:{args}})"
                                      "MERGE (invokename:Method {name:{invokename}})")
                                    
                                    "MERGE (invokepackage)-[:CONTAIN]->(invokeclass)-[:CONTAIN]->(invokename)"
                                    "MERGE (callback)-[:EXPLICIT_INVOKE]->(invokename)"])
                         (merge {:callbackname (str class-name "." callback-name)
                                 :invokepackagename invoke-package-name
                                 :invokeclassname invoke-class-name
                                 :invokename (str invoke-class-name "." invoke-name)}
                                (if args
                                  {:args args}
                                  {})))]))))
                ;; implicit control flow
                (let [path (conj path :implicit)]
                  (doseq [callback-invoke (get-in dex path)]
                    (let [invoke-package-name (:package callback-invoke)
                          invoke-class-name (:class callback-invoke)
                          invoke-name (:method callback-invoke)
                          args (:args callback-invoke)]
                      (ntx/execute
                       conn transaction
                       [(ntx/statement
                         (str/join " "
                                   ["MERGE (callback:Method:Callback {name:{callbackname}})"
                                    "MERGE (invokepackage:Package {name:{invokepackagename}})"
                                    "MERGE (invokeclass:Class {name:{invokeclassname}})"
                                    (if args
                                      "MERGE (invokename:Method {name:{invokename},args:{args}})"
                                      "MERGE (invokename:Method {name:{invokename}})")
                                    
                                    "MERGE (invokepackage)-[:CONTAIN]->(invokeclass)-[:CONTAIN]->(invokename)"
                                    "MERGE (callback)-[:IMPLICIT_INVOKE]->(invokename)"])
                         (merge {:callbackname (str class-name "." callback-name)
                                 :invokepackagename invoke-package-name
                                 :invokeclassname invoke-class-name
                                 :invokename (str invoke-class-name "." invoke-name)}
                                (if args
                                  {:args args}
                                  {})))]))))
                ;; invokes that descend from Android API
                (let [path (conj path :descend)]
                  (doseq [[api-invoke callback-invokes] (get-in dex path)]
                    (let [api-package-name (:package api-invoke)
                          api-class-name (:class api-invoke)
                          api-name (:method api-invoke)]
                      (ntx/execute
                       conn transaction
                       [(ntx/statement
                         (str/join " "
                                   ["MERGE (apipackage:Package {name:{apipackagename}})"
                                    "MERGE (apiclass:Class {name:{apiclassname}})"
                                    "MERGE (apiname:Method {name:{apiname}})"
                                    "MERGE (apipackage)-[:CONTAIN]->(apiclass)-[:CONTAIN]->(apiname)"])
                         {:apipackagename api-package-name
                          :apiclassname api-class-name
                          :apiname (str api-class-name "." api-name)})])
                      (doseq [callback-invoke callback-invokes]
                        (let [invoke-package-name (:package callback-invoke)
                              invoke-class-name (:class callback-invoke)
                              invoke-name (:method callback-invoke)]
                          (ntx/execute
                           conn transaction
                           [(ntx/statement
                             (str/join " "
                                       ["MERGE (apiname:Method {name:{apiname}})"
                                        "MERGE (invokename:Method {name:{invokename}})"
                                        "MERGE (apiname)<-[:DESCEND]-(invokename)"])
                             (merge {:apiname (str api-class-name "." api-name)
                                     :invokename (str invoke-class-name "." invoke-name)}))])))))))))))
      
      ;; app components
      (doseq [comp-type [:activity :service :receiver]]
        (doseq [[comp-name {:keys [intent-filter-action
                                   intent-filter-category]}]
                (->> manifest
                     comp-type)]
          (let [comp-name (name comp-name)
                intent-filter-action (map name intent-filter-action)
                intent-filter-category (map name intent-filter-category)]
            (ntx/execute
             conn transaction
             [(ntx/statement
               (str/join " "
                         ["MERGE (dex:Dex {sha256:{dexsha256}})"
                          "MERGE (ic:Class {name:{compname}})"
                          (format "SET ic:%1$s:Component"
                                  (->> comp-type name str/capitalize))
                          "MERGE (dex)-[:CONTAIN]->(ic)"
                          "FOREACH ("
                          "action IN {intentfilteraction} |"
                          "  MERGE (n:IntentFilterAction {name:action})"
                          "  MERGE (n)-[:TRIGGER]->(ic)"
                          ")"
                          "FOREACH ("
                          "category IN {intentfiltercategory} |"
                          "  MERGE (n:IntentFilterCategory {name:category})"
                          "  MERGE (n)-[:TRIGGER]->(ic)"
                          ")"
                          ])
               {:dexsha256 dex-sha256
                :compname comp-name
                :intentfilteraction intent-filter-action
                :intentfiltercategory intent-filter-category})]))))
      
      ;; any more query within the transaction?
      )))

(let [common (fn [apk tags options op]
               (when-not (empty? tags)
                 (let [statements (atom [])
                       apk-sha256 (:sha256 apk)]
                   (doseq [[types prop] tags]
                     (swap! statements conj
                            (ntx/statement
                             (str/join " "
                                       ["MATCH (a:Apk {sha256:{apksha256}})"
                                        (format "MERGE (l:%1$s:Tag {id:{prop}.id})"
                                                (->> types
                                                     ;; to satisfy Neo4j identifier requirement
                                                     (map #(-> (str %)
                                                               (str/replace #"\s+" "")
                                                               (str/replace #"-" "_")))
                                                     (str/join ":")))
                                        "SET l={prop}"
                                        "MERGE (l)-[r:TAG]->(a)"
                                        (case op
                                          :untag "DELETE r"
                                          :tag ""
                                          "")])
                             {:apksha256 apk-sha256
                              :prop prop})))
                   (let [conn (connect options)
                         transaction (ntx/begin-tx conn)]
                     (try
                       (ntx/commit conn transaction @statements)
                       (catch Exception e
                         (print-stack-trace e)))))))]
  
  (defn tag-apk
  "tag an existing Apk node with the tags"
  [apk tags
   {:keys [] :as options}]
  (common apk tags options :tag))
  (defn untag-apk
  "untag an existing Apk node with the tags"
  [apk tags
   {:keys [] :as options}]
  (common apk tags options :untag)))

(defn create-index
  "create index"
  [{:keys []
    :as options}]
  (let [statements (map ntx/statement
                        (map (fn [[label prop]]
                               (str "CREATE INDEX ON :"
                                    label "(" prop ")"))
                             {"SigningKey" "sha256"
                              "Apk" "sha256"
                              "Dex" "sha256"
                              "Permission" "name"
                              "Package" "name"
                              "Class" "name"
                              "Method" "name"
                              "Callback" "name"
                              "Activity" "name"
                              "Service" "name"
                              "Receiver" "name"
                              "IntentFilterAction" "name"
                              "IntentFilterCategory" "name"
                              "AndroidAPI" "name"
                              "Tag" "id"}))]
    (let [conn (connect options)
          transaction (ntx/begin-tx conn)]
      (ntx/commit conn transaction statements))))

(defn mark-android-api
  "label =~'^(?:com.)?android' nodes as AndroidAPI; should be infrequently used"
  [{:keys []
    :as options}]
  (let [conn (connect options)
        transaction (ntx/begin-tx conn)]
    (ntx/with-transaction
      conn
      transaction
      true
      (ntx/execute conn transaction
                   [(ntx/statement
                     (str/join " "
                               ["MATCH (n)"
                                "WHERE n.name=~{regex}"
                                "SET n:AndroidAPI"])
                     {:regex "L?(?:android\\.|com\\.android\\.|dalvik\\.).*"})]))))

(defn connect
  "connect to local neo4j server at PORT"
  [{:keys [neo4j-port neo4j-protocol
           neo4j-conn-backoff
           verbose]
    :as options
    :or {neo4j-port (:neo4j-port @defaults)
         neo4j-protocol (:neo4j-protocol @defaults)}}]
  (let [port (if neo4j-port neo4j-port (:neo4j-port @defaults))
        protocol (if neo4j-protocol neo4j-protocol (:neo4j-protocol @defaults))
        retry (atom nil)
        conn (atom nil)]
    (loop []
      (try
        (reset! conn (nr/connect (format "%1$s://localhost:%2$d/db/data/" protocol port)))
        (reset! retry false)
        ;; java.io.IOException catches java.net.SocketException and other situations
        (catch java.io.IOException e
          (let [backoff (rand-int neo4j-conn-backoff)]
            (when (and verbose (> verbose 1))
              (binding [*out* *err*]
                (println "Neo4j connection exception, retry in"
                         backoff
                         "seconds")))
            (Thread/sleep (* backoff 1000)))
          (reset! retry true)))
      (when @retry
        (recur)))
    @conn))


(defn android-api?
  "test whether NAME is part of Android API"
  [name]
  (let [name (str name)]
    (re-find #"^L?(?:android\.|com\.android\.|dalvik\.)" name)))

