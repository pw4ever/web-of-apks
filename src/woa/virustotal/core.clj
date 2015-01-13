(ns woa.virustotal.core
  "https://www.virustotal.com/en/documentation/public-api/"
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
  (:require [clj-http.client :as http-client]
            [clojure.data.json :as json]))

;;; declaration

(declare submit-file
         request-rescan
         make-report-result-into-tags get-report
         ;; plumbing
         jsonfy-map clojurefy-map
         interpret-response-code interpret-status)

;;; implementation

;;; porcelain

(defn submit-file
  "submit file for checking"
  [{:keys [file-content]
    :as resource}
   {:keys [virustotal-apikey]
    :as options}]
  (let [url "https://www.virustotal.com/vtapi/v2/file/scan"]
    ;; basic safety check
    (when (and file-content)
      (let [{:keys [status body]
             :as http-response}
            (http-client/post url
                              {:multipart [{:name "apikey"
                                            :content virustotal-apikey}
                                           {:name "file"
                                            :content file-content}]
                               :throw-exceptions false})

            i-status (interpret-status status)]
        (if (= i-status :status-ok)
          (let [result (->> body json/read-str clojurefy-map)
                {:keys [response-code]} result
                i-response-code (interpret-response-code response-code)]
            (if (= i-response-code :response-ok)
              (assoc-in result [:response-code]
                        i-response-code)
              i-response-code))
          i-status)))))

(defn request-rescan
  "obtain report result"
  [{:keys [md5 sha1 sha256 scan-id]
    :as resource}
   {:keys [virustotal-apikey]
    :as options}]
  (let [url "https://www.virustotal.com/vtapi/v2/file/rescan"]
    (when-let [resource (or md5 sha1 sha256 scan-id)]
      (let [{:keys [status body]
             :as http-response}
            (http-client/post url
                              {:form-params {:apikey virustotal-apikey
                                             :resource resource}
                               :throw-exceptions false})

            i-status (interpret-status status)]
        (if (= i-status :status-ok)
          (let [result (->> body json/read-str clojurefy-map)
                {:keys [response-code]} result
                i-response-code (interpret-response-code response-code)]
            (if (= i-response-code :response-ok)
              (assoc-in result [:response-code]
                        i-response-code)
              i-response-code))
          i-status)))))


(defn make-report-result-into-tags
  "make report-result into the form suitable to supply as app :tags on command-line"
  [report-result]
  (when-let [scans (:scans report-result)]
    (->> scans
         (filter (fn [[_ v]]
                   (get v "detected")))
         (map (fn [[k v]]
                [["Malware" "VirusTotal"]
                 (let [result (get v "result")]
                   (merge (dissoc v "detected")
                          {"id" (str/join "-"
                                          ["malware" k result])
                           "source" k}))]))
         vec)))

(defn get-report
  "obtain report result"
  [{:keys [md5 sha1 sha256 scan-id]
    :as resource}
   {:keys [virustotal-apikey]
    :as options}]
  (let [url "https://www.virustotal.com/vtapi/v2/file/report"]
    (when-let [resource (or md5 sha1 sha256 scan-id)]
      (let [{:keys [status body]
             :as http-response}
            (http-client/post url
                              {:form-params {:apikey virustotal-apikey
                                             :resource resource}
                               :throw-exceptions false})

            i-status (interpret-status status)]
        (if (= i-status :status-ok)
          (let [result (->> body json/read-str clojurefy-map)
                {:keys [response-code]} result
                i-response-code (interpret-response-code response-code)]
            (if (= i-response-code :response-ok)
              (assoc-in result [:response-code]
                        i-response-code)
              i-response-code))
          i-status)))))

;;; plumbing

(defn interpret-response-code
  "interpret HTTP response code from VirusTotal"
  [response-code]
  (case response-code
    0 :response-not-found
    1 :response-ok
    -2 :response-still-queued
    (list :response-code response-code)))


(defn interpret-status
  "interpret HTTP status from VirusTotal"
  [status]
  (case status
    200 :status-ok
    204 :status-exceed-api-limit
    403 :status-exceed-priviledge
    (list :status status)))

(defn jsonfy-map
  "use underscored string as key"
  [the-map]
  (->> the-map
       (map (fn [[k v]]
              [(-> (cond
                     (keyword? k) (name k)
                     :otherwise (str k))
                   (str/replace "-" "_"))
               v]))
       (into {})))

(defn clojurefy-map
  "use dashed keyword as key"
  [the-map]
  (->> the-map
       (map (fn [[k v]]
              [(-> k
                   (str/replace "_" "-")
                   keyword)
               v]))
       (into {})))

