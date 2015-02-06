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
         add-to-batch-csv dump-batch-csv
         tag-apk untag-apk
         create-index mark-android-api
         connect android-api?)

(def defaults (atom {:neo4j-port 7474
                     :neo4j-protocol "http"}))

(let [node-props (atom #{})
      rel-props (atom #{})
      node-counter (atom -1)
      nodes (atom {}) ; node => node-counter
      rels (atom {})
      merge-node (fn [[labels props :as node]]
                   (swap! node-props into (keys props))
                   (when-not (get @nodes node)
                     (swap! nodes assoc node (swap! node-counter inc))))
      node-updates (atom {})
      update-node (fn [old-node [labels props :as new-node]]
                    (when-let [id (get @nodes old-node)]
                      (swap! node-props into (keys props))
                      ;; cache the updates
                      (swap! node-updates assoc old-node new-node)))
      merge-rel (fn [node1 [labels props :as rel] node2]
                  (let [n1 (get @nodes node1)
                        n2 (get @nodes node2)]
                    (when (and n1 n2)
                      (swap! rel-props into (keys props))
                      (swap! rels update-in [[n1 n2]]
                             #(->> (conj %1 %2) set)
                             rel))))]
  (defn add-to-batch-csv
  "add to batch csv that is to be dumped later"
  [apk
   {:keys [neo4j-include-methodinstance]
    :as options}]
  (let [manifest (:manifest apk)
        dex-sha256 (:dex-sha256 apk)
        cert-sha256 (:cert-sha256 apk)
        apk-sha256 (:sha256 apk)
        apk-package (:package manifest)
        apk-version-name (:android:versionName manifest)
        apk-version-code (:android:versionCode manifest)
        the-dex (:dex apk)]
    (let [signing-key [["SigningKey"] {"sha256" cert-sha256}]
          apk [["Apk"] {"sha256" apk-sha256
                        "package" apk-package
                        "versionCode" apk-version-code
                        "versionName" apk-version-name}]
          dex [["Dex"] {"sha256" dex-sha256}]]
      (merge-node signing-key)
      (merge-node apk)
      (merge-node dex)
      (merge-rel signing-key [["SIGN"] nil] apk)
      (merge-rel apk [["CONTAIN"] nil] dex)
      
      ;; permissions
      (doseq [perm (->> manifest :uses-permission (map name))]
        (let [n [["Permission"] {"name" perm}]]
          (merge-node n)
          (merge-rel apk [["USE"] nil] n)))
      (doseq [perm (->> manifest :permission (map name))]
        (let [n [["Permission"] {"name" perm}]]
          (merge-node n)
          (merge-rel apk [["DEFINE"] nil] n)))

      ;; component package and class
      (dorun
       (for [comp-package-name (->> the-dex keys)]
         (let [comp-package [["Package"] {"name" comp-package-name}]]
           (merge-node comp-package)
           (dorun
            (for [comp-class-name (->> (get-in the-dex [comp-package-name]) keys)]
              (let [comp-class [["Class"] {"name" comp-class-name}]]
                (merge-node comp-class)
                (merge-rel comp-package [["CONTAIN"] nil] comp-class)
                (merge-rel dex [["CONTAIN"] nil] comp-class)
                
                (let [{:keys [android-api-ancestors callbacks]}
                      (->> (get-in the-dex [comp-package-name comp-class-name]))]
                  (dorun
                   (for [ancestor android-api-ancestors]
                     (let [ancestor-package-name (:package ancestor)
                           ancestor-package [["Package"] {"name" ancestor-package-name}]
                           ancestor-class-name (:class ancestor)
                           ancestor-class [["Class"] {"name" ancestor-class-name}]]
                       (merge-node ancestor-package)
                       (merge-node ancestor-class)
                       (merge-rel ancestor-package [["CONTAIN"] nil] ancestor-class)
                       (merge-rel comp-class [["DESCEND"] nil] ancestor-class))))

                  (dorun
                   (for [callback-name (->> callbacks keys)]
                     (let [callback [["Method" "Callback"]
                                     {"name" (str comp-class-name "." callback-name)}]]
                       (merge-node callback)
                       (merge-rel comp-class [["CONTAIN"] nil] callback)
                       (let [path [comp-package-name comp-class-name :callbacks callback-name]]
                         
                         ;; explicit control flow
                         (let [path (conj path :explicit)]
                           ;; deduplication
                           (let [callback-invokes (->> (get-in the-dex path)
                                                       (map #(select-keys % [:package :class :method]))
                                                       (into #{}))]
                             (dorun
                              (for [callback-invoke callback-invokes]
                                (let [invoke-package-name (:package callback-invoke)
                                      invoke-package [["Package"] {"name" invoke-package-name}]
                                      invoke-class-name (:class callback-invoke)
                                      invoke-class [["Class"] {"name" invoke-class-name}]
                                      invoke-name (:method callback-invoke)
                                      invoke [["Method"]
                                              {"name" (str invoke-class-name "." invoke-name)}]]
                                  (merge-node invoke-package)
                                  (merge-node invoke-class)
                                  (merge-node invoke)
                                  (merge-rel invoke-package [["CONTAIN"] nil] invoke-class)
                                  (merge-rel invoke-class [["CONTAIN"] nil] invoke)
                                  (merge-rel callback [["EXPLICIT_INVOKE"] nil] invoke)
                                  (merge-rel invoke [["INVOKED_BY"] nil] apk)))))
                           (when neo4j-include-methodinstance
                             (dorun
                              (for [callback-invoke (get-in the-dex path)]
                                (let [invoke-class-name (:class callback-invoke)
                                      invoke-class [["Class"] {"name" invoke-class-name}]
                                      invoke-name (:method callback-invoke)
                                      args (:args callback-invoke)
                                      invoke [["Method"] {"name" invoke-name}]
                                      invoke-instance [["MethodInstance"]
                                                       {"name" (str invoke-class-name "." invoke-name)
                                                        "args" args}]]
                                  (merge-node invoke-instance)
                                  (merge-rel invoke-instance [["INSTANCE_OF"] nil] invoke)
                                  (merge-rel callback [["EXPLICIT_INVOKE"] nil] invoke-instance))))))

                         ;; implicit control flow
                         (let [path (conj path :implicit)]
                           ;; deduplication
                           (let [callback-invokes (->> (get-in the-dex path)
                                                       (map #(select-keys % [:package :class :method]))
                                                       (into #{}))]
                             (dorun
                              (for [callback-invoke callback-invokes]
                                (let [invoke-package-name (:package callback-invoke)
                                      invoke-package [["Package"] {"name" invoke-package-name}]
                                      invoke-class-name (:class callback-invoke)
                                      invoke-class [["Class"] {"name" invoke-class-name}]
                                      invoke-name (:method callback-invoke)
                                      invoke [["Method"]
                                              {"name" (str invoke-class-name "." invoke-name)}]]
                                  (merge-node invoke-package)
                                  (merge-node invoke-class)
                                  (merge-node invoke)
                                  (merge-rel invoke-package [["CONTAIN"] nil] invoke-class)
                                  (merge-rel invoke-class [["CONTAIN"] nil] invoke)
                                  (merge-rel callback [["IMPLICIT_INVOKE"] nil] invoke)
                                  (merge-rel invoke [["INVOKED_BY"] nil] apk)))))
                           (when neo4j-include-methodinstance
                             (dorun
                              (for [callback-invoke (get-in the-dex path)]
                                (let [invoke-class-name (:class callback-invoke)
                                      invoke-class [["Class"] {"name" invoke-class-name}]
                                      invoke-name (:method callback-invoke)
                                      args (:args callback-invoke)
                                      invoke [["Method"] {"name" invoke-name}]
                                      invoke-instance [["MethodInstance"]
                                                       {"name" (str invoke-class-name "." invoke-name)
                                                        "args" args}]]
                                  (merge-node invoke-instance)
                                  (merge-rel invoke-instance [["INSTANCE_OF"] nil] invoke)
                                  (merge-rel callback [["IMPLICIT_INVOKE"] nil] invoke-instance))))))
                         
                         
                         ;; invokes that descend from Android API
                         (let [path (conj path :descend)]
                           (dorun
                            (for [[api-invoke callback-invokes] (get-in the-dex path)]
                              (let [api-package-name (:package api-invoke)
                                    api-package [["Package"] {"name" api-package-name}]
                                    api-class-name (:class api-invoke)
                                    api-class [["Class"] {"name" api-class-name}]
                                    api-name (:method api-invoke)
                                    api [["Method"]
                                         {"name" (str api-class-name "." api-name)}]]
                                (merge-node api-package)
                                (merge-node api-class)
                                (merge-node api)
                                (merge-rel api-package [["CONTAIN"] nil] api-class)
                                (merge-rel api-class [["CONTAIN"] nil] api)
                                (dorun
                                 (for [callback-invoke callback-invokes]
                                   (let [invoke-package-name (:package callback-invoke)
                                         invoke-package [["Package"] {"name" invoke-package-name}]
                                         invoke-class-name (:class callback-invoke)
                                         invoke-class [["Class"] {"name" invoke-class-name}]
                                         invoke-name (:method callback-invoke)
                                         invoke [["Method"]
                                                 {"name" (str invoke-class-name "." invoke-name)}]]
                                     (merge-rel invoke [["DESCEND"] nil] api)))))))))))))))))))

      ;; app components
      (doseq [comp-type [:activity :service :receiver]]
        (doseq [[comp-name {:keys [intent-filter-action
                                   intent-filter-category]}]
                (->> manifest
                     comp-type)]
          (let [comp-name (name comp-name)
                comp [["Class"] {"name" comp-name}]
                new-comp [["Class" "Component" (->> comp-type name str/capitalize)]
                          {"name" comp-name}]
                intent-filter-actions (map name intent-filter-action)
                intent-filter-categories (map name intent-filter-category)]
            (update-node comp new-comp)
            (doseq [intent-filter-action-name intent-filter-actions]
              (let [intent-filter-action [["IntentFilterAction"]
                                          {"name" intent-filter-action-name}]]
                (merge-node intent-filter-action)
                (merge-rel intent-filter-action [["TRIGGER"] nil] comp)))
            (doseq [intent-filter-category-name intent-filter-categories]
              (let [intent-filter-category [["IntentFilterCategory"]
                                            {"name" intent-filter-category-name}]]
                (merge-node intent-filter-category)
                (merge-rel intent-filter-category [["TRIGGER"] nil] comp)))))))))
  
  (defn dump-batch-csv
  "https://github.com/jexp/batch-import/tree/2.1"
  [batch-csv-prefix {:keys [] :as options}]
  ;; do the updates
  (doseq [[old-node new-node] @node-updates]
    (when-let [id (get @nodes old-node)]
      (swap! nodes dissoc old-node)
      (swap! nodes assoc new-node id)))
  (with-open [out (io/writer (str batch-csv-prefix ".nodes"))]
    (binding [*out* out]
      (let [id-to-node (set/map-invert @nodes)
            node-props (seq @node-props)]
        (println (format "%1$s%2$s%3$s"
                         (str/join "\t" node-props)
                         (if node-props "\t" "")
                         "l:label"))
        (dotimes [id (inc @node-counter)]
          (let [[labels props :as node] (get id-to-node id)]
            (println (format "%1$s%2$s%3$s"
                             (str/join "\t"
                                       (map #(get props %)
                                            node-props))
                             (if node-props "\t" "")                             
                             (str/join "," labels))))))))
  (with-open [out (io/writer (str batch-csv-prefix ".rels"))]
    (binding [*out* out]
      (let [rel-props (seq @rel-props)]
        (println (format "start\tend\t%1$s%2$s%3$s"
                         (str/join "\t" rel-props)
                         (if rel-props "\t" "")
                         "l:label"))
        (doseq [rel (->> (keys @rels) sort)]
          (let [[start end] rel]
            (doseq [[labels props] (get @rels rel)]
              (println (format "%1$s\t%2$s\t%3$s%4$s%5$s"
                               start end
                               (str/join "\t"
                                         (map #(get props %)
                                              rel-props))
                               (if rel-props "\t" "")
                               (str/join "," labels)))))))))))

(defn populate-from-parsed-apk
  "populate the database with the parsed apk structure"
  [apk {:keys [neo4j-include-methodinstance]
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

      (ntx/execute
       conn transaction
       (let [result (atom [])]
         (doseq [package-name (->> dex keys)]
           (let [class-names (->> (get-in dex [package-name]) keys)]
             (swap! result conj
                    (ntx/statement
                     (str/join " "
                               ["MERGE (dex:Dex {sha256:{dexsha256}})"
                                "MERGE (package:Package {name:{packagename}})"
                                "FOREACH ("
                                "classname in {classnames} |"
                                "  MERGE (class:Class {name:classname})"
                                "  MERGE (package)-[:CONTAIN]->(class)"
                                "  MERGE (dex)-[:CONTAIN]->(class)"
                                ")"])
                     {:dexsha256 dex-sha256
                      :packagename package-name
                      :classnames class-names}))))
         @result))

      (ntx/execute
       conn transaction
       (let [result (atom [])]
         (doseq [package-name (->> dex keys)]
           (let [class-names (->> (get-in dex [package-name]) keys)]
             (doseq [class-name class-names]
               (let [{:keys [android-api-ancestors callbacks]} (->> (get-in dex [package-name class-name]))]
                 (doseq [base android-api-ancestors]
                   (let [ancestor-package (:package base)
                         ancestor-class (:class base)]
                     (swap! result conj
                            (ntx/statement
                             (str/join " "
                                       ["MERGE (class:Class {name:{classname}})"
                                        "MERGE (ancestorpackage:Package {name:{ancestorpackage}})"
                                        "MERGE (ancestorclass:Class {name:{ancestorclass}})"
                                        "MERGE (ancestorpackage)-[:CONTAIN]->(ancestorclass)"
                                        "MERGE (class)-[:DESCEND]->(ancestorclass)"])
                             {:classname class-name
                              :ancestorpackage ancestor-package
                              :ancestorclass ancestor-class}))))))))
         @result))      

      (ntx/execute
       conn transaction
       (let [result (atom [])]
         (doseq [package-name (->> dex keys)]
           (let [class-names (->> (get-in dex [package-name]) keys)]
             (doseq [class-name class-names]
               (let [{:keys [android-api-ancestors callbacks]} (->> (get-in dex [package-name class-name]))]
                 (doseq [callback-name (->> callbacks keys)]
                   (let [path [package-name class-name :callbacks callback-name]]
                     (swap! result conj
                            (ntx/statement
                             (str/join " "
                                       ["MERGE (class:Class {name:{classname}})"
                                        "MERGE (callback:Method:Callback {name:{callbackname}})"
                                        "MERGE (class)-[:CONTAIN]->(callback)"])
                             {:classname class-name
                              :callbackname (str class-name "." callback-name)}))
                     ;; explicit control flow
                     (let [path (conj path :explicit)]
                       ;; deduplication
                       (let [callback-invokes (->> (get-in dex path)
                                                   (map #(select-keys % [:package :class :method]))
                                                   (into #{}))]
                         (doseq [callback-invoke callback-invokes]
                           (let [invoke-package-name (:package callback-invoke)
                                 invoke-class-name (:class callback-invoke)
                                 invoke-name (:method callback-invoke)]
                             (swap! result conj
                                    (ntx/statement
                                     (str/join " "
                                               ["MERGE (apk:Apk {sha256:{apksha256}})"
                                                "MERGE (callback:Callback {name:{callbackname}})"
                                                "MERGE (invokepackage:Package {name:{invokepackagename}})"
                                                "MERGE (invokeclass:Class {name:{invokeclassname}})"
                                                "MERGE (invoke:Method {name:{invokename}})"
                                                "MERGE (invokepackage)-[:CONTAIN]->(invokeclass)-[:CONTAIN]->(invoke)"
                                                "MERGE (callback)-[:EXPLICIT_INVOKE]->(invoke)"
                                                ;; to quickly find Apk from Method
                                                "MERGE (apk)<-[:INVOKED_BY]-(invoke)"])
                                     {:apksha256 apk-sha256
                                      :callbackname (str class-name "." callback-name)
                                      :invokepackagename invoke-package-name
                                      :invokeclassname invoke-class-name
                                      :invokename (str invoke-class-name "." invoke-name)})))))
                       (when neo4j-include-methodinstance
                         (doseq [callback-invoke (get-in dex path)]
                           (let [invoke-class-name (:class callback-invoke)
                                 invoke-name (:method callback-invoke)
                                 args (:args callback-invoke)]
                             (swap! result conj
                                    (ntx/statement
                                     (str/join " "
                                               ["MERGE (callback:Callback {name:{callbackname}})"
                                                "MERGE (invoke:Method {name:{invokename}})"
                                                "MERGE (invokeinst:MethodInstance {name:{invokename},args:{args}})"
                                                "MERGE (invoke)<-[:INSTANCE_OF]-(invokeinst)"
                                                "MERGE (callback)-[:EXPLICIT_INVOKE]->(invokeinst)"])
                                     {:callbackname (str class-name "." callback-name)
                                      :invokename (str invoke-class-name "." invoke-name)
                                      :args args}))))))
                     ;; implicit control flow
                     (let [path (conj path :implicit)]
                       ;; deduplication
                       (let [callback-invokes (->> (get-in dex path)
                                                   (map #(select-keys % [:package :class :method]))
                                                   (into #{}))]
                         (doseq [callback-invoke callback-invokes]
                           (let [invoke-package-name (:package callback-invoke)
                                 invoke-class-name (:class callback-invoke)
                                 invoke-name (:method callback-invoke)]
                             (swap! result conj
                                    (ntx/statement
                                     (str/join " "
                                               ["MERGE (apk:Apk {sha256:{apksha256}})"
                                                "MERGE (callback:Callback {name:{callbackname}})"
                                                "MERGE (invokepackage:Package {name:{invokepackagename}})"
                                                "MERGE (invokeclass:Class {name:{invokeclassname}})"
                                                "MERGE (invoke:Method {name:{invokename}})"
                                                "MERGE (invokepackage)-[:CONTAIN]->(invokeclass)-[:CONTAIN]->(invoke)"
                                                "MERGE (callback)-[:IMPLICIT_INVOKE]->(invoke)"
                                                ;; to quickly find Apk from Method
                                                "MERGE (apk)<-[:INVOKED_BY]-(invoke)"])
                                     {:apksha256 apk-sha256
                                      :callbackname (str class-name "." callback-name)
                                      :invokepackagename invoke-package-name
                                      :invokeclassname invoke-class-name
                                      :invokename (str invoke-class-name "." invoke-name)})))))
                       (when neo4j-include-methodinstance
                         (doseq [callback-invoke (get-in dex path)]
                           (let [invoke-class-name (:class callback-invoke)
                                 invoke-name (:method callback-invoke)
                                 args (:args callback-invoke)]
                             (swap! result conj
                                    (ntx/statement
                                     (str/join " "
                                               ["MERGE (callback:Callback {name:{callbackname}})"
                                                "MERGE (invoke:Method {name:{invokename}})"
                                                "MERGE (invokeinst:MethodInstance {name:{invokename},args:{args}})"
                                                "MERGE (invoke)<-[:INSTANCE_OF]-(invokeinst)"
                                                "MERGE (callback)-[:IMPLICIT_INVOKE]->(invokeinst)"])
                                     {:callbackname (str class-name "." callback-name)
                                      :invokename (str invoke-class-name "." invoke-name)
                                      :args args}))))))
                     ;; invokes that descend from Android API
                     (let [path (conj path :descend)]
                       (doseq [[api-invoke callback-invokes] (get-in dex path)]
                         (let [api-package-name (:package api-invoke)
                               api-class-name (:class api-invoke)
                               api-name (:method api-invoke)]
                           (swap! result conj
                                  (ntx/statement
                                   (str/join " "
                                             ["MERGE (apipackage:Package {name:{apipackagename}})"
                                              "MERGE (apiclass:Class {name:{apiclassname}})"
                                              "MERGE (apiname:Method {name:{apiname}})"
                                              "MERGE (apipackage)-[:CONTAIN]->(apiclass)-[:CONTAIN]->(apiname)"])
                                   {:apipackagename api-package-name
                                    :apiclassname api-class-name
                                    :apiname (str api-class-name "." api-name)}))
                           (doseq [callback-invoke callback-invokes]
                             (let [invoke-package-name (:package callback-invoke)
                                   invoke-class-name (:class callback-invoke)
                                   invoke-name (:method callback-invoke)]
                               (swap! result conj
                                      (ntx/statement
                                       (str/join " "
                                                 ["MERGE (apiname:Method {name:{apiname}})"
                                                  "MERGE (invokename:Method {name:{invokename}})"
                                                  "MERGE (apiname)<-[:DESCEND]-(invokename)"])
                                       (merge {:apiname (str api-class-name "." api-name)
                                               :invokename (str invoke-class-name "." invoke-name)}))))))))))))))         
         
         @result))
      
      ;; app components
      (ntx/execute
       conn transaction
       (let [result (atom [])]
         (doseq [comp-type [:activity :service :receiver]]
           (doseq [[comp-name {:keys [intent-filter-action
                                      intent-filter-category]}]
                   (->> manifest
                        comp-type)]
             (let [comp-name (name comp-name)
                   intent-filter-action (map name intent-filter-action)
                   intent-filter-category (map name intent-filter-category)]
               (swap! result conj
                      (ntx/statement
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
                        :intentfiltercategory intent-filter-category})))))         
         @result))
      
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
                              "MethodInstance" "name"
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

