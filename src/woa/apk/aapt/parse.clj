(ns woa.apk.aapt.parse
  ;; internal libs
  ;; common libs
  (:require [clojure.string :as str]
            [clojure.set :as set]
            [clojure.walk :as walk]
            [clojure.zip :as zip]
            [clojure.java.io :as io]
            [clojure.pprint :refer [pprint print-table]]
            [clojure.stacktrace :refer [print-stack-trace]])  
  ;; special libs
  (:require [clojure.java.shell :as shell :refer [sh]]))

(def manifest "AndroidManifest.xml")

;; porcelain
(declare get-badging get-manifest)
(declare decompile-xml get-manifest-xml)

;; plumbing
(declare parse-aapt-xmltree
         get-nodes-from-parsed-xmltree)
(declare aapt-dump-xmltree
         aapt-dump-badging
         aapt-dump-manifest)

(defn get-badging
  "get badging in Clojure data structure"
  [apk]
  (let [result (atom {})
        get-string-in-single-quotes #(if-let [[_ meat] (re-find #"^'([^']+)'$" %)]
                                       meat
                                       %)]
    ;; first pass
    (doseq [line (str/split-lines (aapt-dump-badging apk))]
      ;; only consider lines that have values
      (when-let [[_ label content] (re-find #"^([^:]+):([^:]+)$" line)]
        (let [label (keyword label)]
          (swap! result update-in [label]
                 conj content))))
    ;; second pass
    (doseq [k (keys @result)]
      (swap! result update-in [k]
             (fn [content]
               (when-let [first-item (first content)]
                 (cond
                  ;; strings
                  (re-matches #"'[^']+'" first-item)
                  (into #{}
                        (map get-string-in-single-quotes
                             content))
                  ;; map
                  (re-matches #"(?:\s[^\s'][^\s=]+='[^']+')+" first-item)
                  (into {}
                        (for [[_ k v] (re-seq #"\s([^\s=]+)='([^']+)'" first-item)]
                          [(keyword k)
                           v]))
                  ;; set
                  (re-matches #"(?:\s'[^']+')+" first-item)
                  (into #{}
                        (for [[_ v] (re-seq #"\s'([^']+)'" first-item)]
                          v))
                  ;; sequence
                  (re-matches #"'[^']+',.+" first-item)
                  (into #{}
                        (map #(into []
                                    (map (fn [[_ meat]]
                                           meat)
                                         (re-seq #"'([^']+)',?" %)))
                             content)))))))
    @result))

(defn get-manifest
  "get manifest in Clojure data structure

reference: https://developer.android.com/guide/topics/manifest/manifest-intro.html"
  [apk]
  (let [parsed-manifest (parse-aapt-xmltree (aapt-dump-manifest apk))
        result (atom {})
        get-node-android-name (fn [node package]
                                (-> node
                                  (get-in [:attrs :android:name])
                                  str
                                  (#(if (.startsWith ^String % ".")
                                      (str package %)
                                      %))
                                  keyword))]
    ;; <manifest> attrs
    (let [node (first (get-nodes-from-parsed-xmltree parsed-manifest
                                                     [:manifest]))]
      (doseq [attr [:android:versionCode
                    :android:versionName
                    :package]]
        (swap! result assoc-in [attr]
               (get-in node [:attrs attr]))))
    (let [package (get-in @result [:package])]
      ;; <manifest> level
      (doseq [node [:uses-permission
                    :permission]]
        (swap! result assoc-in [node]
               (set (map #(get-node-android-name % package)
                         (get-nodes-from-parsed-xmltree parsed-manifest
                                                        [:manifest node])))))
      ;; <application> level
      (doseq [node [:activity
                    :activity-alias
                    :service
                    :receiver]]
        (swap! result assoc-in [node]
               (into {}
                     (map (fn [node]
                            {(get-node-android-name node package)
                             (into {}
                                   (map (fn [intent-filter-tag]
                                          [(keyword (str "intent-filter-"
                                                         (name intent-filter-tag)))
                                           (set (map #(get-node-android-name % package)
                                                     (get-nodes-from-parsed-xmltree (:content node)
                                                                                    [:intent-filter
                                                                                     intent-filter-tag])))])
                                        [:action :category]))})
                          (get-nodes-from-parsed-xmltree parsed-manifest
                                                         [:manifest :application node]))))))
    @result))

(defn get-manifest-xml
  "get manifest in XML format"
  [apk]
  (decompile-xml apk manifest))

(defn decompile-xml
  "decompile the binary xml on PATH in APK"
  [apk path]
  (let [xmltree (parse-aapt-xmltree (aapt-dump-xmltree apk path))
        xmltree-to-xml (fn xmltree-to-xml [indent nodes]
                         (when (not-empty nodes)
                           (doseq [node nodes]
                             (let [tag (:tag node)
                                   attrs (:attrs node)
                                   content (:content node)
                                   indent-str (apply str (repeat indent " "))]
                               (printf "%s<%s%s"
                                       indent-str
                                       (name tag)
                                       (if-not (empty? attrs)
                                         (str " "
                                              (str/join " "
                                                        (map (fn [[k v]]
                                                               (if (and k v)
                                                                 (format "%s=\"%s\""
                                                                         (name k) v)
                                                                 ""))
                                                             attrs)))
                                         ""))
                               (if (not-empty content)
                                 (do
                                   (println ">")
                                   (xmltree-to-xml (+ indent 2)
                                                   content)
                                   (printf "%s</%s>\n"
                                           indent-str
                                           (name tag)))
                                 (println " />"))))))]
    (with-out-str
      (println "<?xml version=\"1.0\" encoding=\"utf-8\"?>")
      (xmltree-to-xml 0 xmltree))))

(defn parse-aapt-xmltree
  "parse aapt xmltree dump into Clojure data structure"
  [xmltree-dump]
  (let [lines (vec (map #(let [[_ spaces type raw]
                               (re-find #"^(\s*)(\S):\s(.+)$"
                                        %)]
                           {:indent (count spaces)
                            :type type
                            :raw raw})
                        (str/split-lines xmltree-dump)))
        ;; first pass build: from lines to a tree        
        build (fn build [lines]
                (when-let [lines (vec lines)]
                  (when (not (empty? lines))
                    (let [start-indent (:indent (first lines))
                          segment-indexes (vec (concat (keep-indexed #(when (<= (:indent %2)
                                                                                start-indent)
                                                                        %1)
                                                                     lines)
                                                       [(count lines)]))
                          segments (map #(subvec lines
                                                 (get segment-indexes %)
                                                 (get segment-indexes (inc %)))
                                        (range (dec (count segment-indexes))))]
                      (->> segments
                           (map (fn [lines]
                                   (let [line (first lines)
                                         lines (rest lines)
                                         type (:type line)
                                         raw (:raw line)]
                                     (case type
                                       ;; Namespace
                                       "N"
                                       (let [[_ n v] (re-find #"^([^=]+)=([^=]+)$" raw)]
                                         {:type :namespace
                                          :name (str "xmlns:" n)
                                          :value v
                                          :children (build lines)}) 
                                       ;; Element
                                       "E"
                                       (let [[_ name line] (re-find #"^(\S+)\s+\(line=(\d+)\)$"
                                                                    raw)]
                                         {:type :element
                                          :name name
                                          :line line
                                          :children (build lines)})
                                       ;; Attribute
                                       "A"
                                       (let [[_
                                              encoded-name bare-name
                                              quoted-value encoded-value bare-value] (re-find
                                              #"(?x)
^(?:
  ([^=(]+)\([^)]+\)| # encoded name
  ([^=(]+) # bare name
)
=
(?:
  \"([^\"]+)\"| # quoted value
  \([^)]+\)(\S+)|  # encoded value
  ([^\"(]\S*) # bare value
)
"
                                              raw)]
                                         {:type :attribute
                                          :name (or bare-name encoded-name)
                                          :value (or quoted-value encoded-value bare-value)})
                                       ;; falls through
                                       nil))))
                           (keep identity)
                           vec)))))
        pass (build lines)]
    (let [;; second pass: merge namespace/attributes into elements
          build (fn build [node & [immediate-namespace]]
                  (case (:type node)
                    ;; element
                    :element
                    (let [[attrs elems] (split-with #(= (:type %) :attribute)
                                                    (:children node))]
                      {:tag (keyword (:name node))
                       :attrs (let [attrs (into {} (map #(do [(keyword (:name %))
                                                              (:value %)])
                                                        attrs))]
                                (if immediate-namespace
                                  (assoc attrs (:name immediate-namespace)
                                         (:value immediate-namespace))
                                  attrs))
                       :content (set (map build elems))})                    
                    ;; namespace
                    :namespace
                    (build (first (:children node))
                           ;; pass the immediate-namespace to its children
                           (select-keys node [:name :value]))))
          pass (set (map build pass))]
      pass)))

(defn get-nodes-from-parsed-xmltree
  "get nodes from parsed xmltree"
  [parsed-xmltree [tag & more-tags]]
  (->> parsed-xmltree
       (filter #(= (:tag %) tag))
       ((fn [nodes]
          (if more-tags
            (mapcat #(get-nodes-from-parsed-xmltree (:content %)
                                                    more-tags)
                    nodes)
            nodes)))
       set))

(defn aapt-dump-xmltree
  "aapt dump xmltree asset"
  [apk asset]
  (:out (sh "aapt" "dump" "xmltree"
            apk asset)))

(defn aapt-dump-badging
  "aapt dump badging apk"
  [apk]
  (:out (sh "aapt" "dump" "badging"
            apk)))

(defn aapt-dump-manifest
  "aapt dump xmltree <manifest>"
  [apk]
  (aapt-dump-xmltree apk manifest))
