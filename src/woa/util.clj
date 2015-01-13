(ns woa.util
  ;; common libs
  (:require [clojure.string :as str]
            [clojure.set :as set]
            [clojure.walk :as walk]
            [clojure.zip :as zip]
            [clojure.java.io :as io]
            [clojure.pprint :refer [pprint print-table]]
            [clojure.stacktrace :refer [print-stack-trace]])
  ;; imports
  )

;;; declaration

(declare print-stack-trace-if-verbose)

;;; implementation

(defn print-stack-trace-if-verbose
  "print-stack-trace Exception e to *err* if verbose is non-nil"
  [^Exception e verbose & [level]]
  (when (and verbose
             (or (not level) (> verbose level)))
    (binding [*out* *err*]
      (print-stack-trace e)
      ;; flush is critical for timely output
      (flush))))
