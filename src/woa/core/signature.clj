(ns woa.core.signature
  ;; internal libs
  (:use woa.util)
  (:use woa.core.invoke-path)
  ;; common libs
  (:require [clojure.string :as str]
            [clojure.set :as set]
            [clojure.walk :as walk]
            [clojure.zip :as zip]
            [clojure.java.io :as io]
            [clojure.pprint :refer [pprint print-table]]
            [clojure.stacktrace :refer [print-stack-trace]])
  ;; special libs
  (:require [incanter.stats :as stats]))

;;; declaration

(declare compute-cgdfd-signature compute-cgdfd)

;;; implementation

(defn compute-cgdfd-signature
  "compute the CGDFD-based signature from the input CGDFD (replace NaN with 0)"
  [cgdfd]
  (try
    (let [total (reduce + (vals cgdfd))
          cgdfd (mapcat #(let [[out-degree multiplicity] %]
                           (repeat multiplicity out-degree))
                        cgdfd)]
      ;; filter on NaN
      (->> [total
            (stats/mean cgdfd)
            (stats/sd cgdfd)
            (stats/skewness cgdfd)
            (stats/kurtosis cgdfd)]
           (map #(let [n %]
                   (cond
                     
                     (try
                       (.isNaN n)
                       (catch Exception e false))
                     0
                     
                     :otherwise n)))
           vec))
    (catch Exception e
      (print-stack-trace e)
      nil)))


(defn compute-cgdfd
  "compute CGDFD (Call Graph Degree Frequency Distribution) from the input invoke-paths that represent the CG (Call Graph)"
  [invoke-paths]
  (let [invocatees (invoke-path-get-invocatee-map invoke-paths)
        cgdfd (atom {})]
    (doseq [[_ invocatees] invocatees]
      (swap! cgdfd update-in [(count invocatees)]
             #(let [now %]
                (cond
                  (nil? now) 1
                  :otherwise (inc now)))))
    @cgdfd))



















