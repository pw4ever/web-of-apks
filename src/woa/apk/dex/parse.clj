(ns woa.apk.dex.parse
  (:require [woa.apk.util
             :refer [get-apk-file-bytes get-apk-file-input-stream
                     extract-apk-file
                     get-apk-file-sha256-digest
                     get-file-sha256-digest]])  
  ;; common libs
  (:require [clojure.string :as str]
            [clojure.set :as set]
            [clojure.walk :as walk]
            [clojure.zip :as zip]
            [clojure.java.io :as io]
            [clojure.pprint :refer [pprint print-table]]
            [clojure.stacktrace :refer [print-stack-trace]]))

;;; declaration

;; var
(declare the-dex)

;; func
(declare extract-the-dex-in-apk get-the-dex-sha256-digest)

;;; implementation

(def the-dex "classes.dex")

(defn extract-the-dex-in-apk
  "extract the dex in apk to output-file-name"
  [apk output-file-name]
  (extract-apk-file apk the-dex output-file-name))

(defn get-the-dex-sha256-digest
  "get sha256 digest of the dex in apk"
  [apk]
  (get-apk-file-sha256-digest apk the-dex))
