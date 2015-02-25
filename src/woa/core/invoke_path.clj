(ns woa.core.invoke-path
  ;; internal libs
  (:use woa.util)
  ;; common libs
  (:require [clojure.string :as str]
            [clojure.set :as set]
            [clojure.walk :as walk]
            [clojure.zip :as zip]
            [clojure.java.io :as io]
            [clojure.pprint :refer [pprint print-table]]
            [clojure.stacktrace :refer [print-stack-trace]])
  ;; special libs
  )

;;; declaration

(declare invoke-path-get-invocatee-map
         invoke-path-get-node
         invoke-path-get-descendants
         invoke-path-get-node-name)

;;; implementation

(defn invoke-path-get-invocatee-map
  "invocatee map is a map from nodes to their invocatees"
  [invoke-paths]
  (let [invocatees (atom {})]
    (process-worklist
     #{invoke-paths}
     (fn [worklist]
       (let [new-worklist (atom #{})]
         (dorun
          (for [work worklist]
            (let [node (invoke-path-get-node work)
                  descendants (invoke-path-get-descendants work)
                  children (map invoke-path-get-node descendants)]
              (swap! invocatees update-in [node]
                     #(->> (into %1 %2) set)
                     children)
              (swap! new-worklist into descendants))))
         @new-worklist)))
    @invocatees))

(defn invoke-path-get-node [invoke-paths]
  (cond
    (map? invoke-paths) (->> invoke-paths keys first)
    :otherwise invoke-paths))


(defn invoke-path-get-descendants [invoke-paths]
  (cond
    (map? invoke-paths) (->> invoke-paths vals first)
    :otherwise nil))

(defn invoke-path-get-node-name [node]
  (cond
    ;; Soot signature format
    (re-matches #"^<.+>$" node)
    (let [[_ class method]
          (re-find #"^<([^:]+):\s+\S+\s+([^(]+)\("
                   node)]
      (str class "." method))

    (re-matches #"^[^<].+\[.+\]" node)
    (let [[_ classmethod]
          (re-find #"^(.+)\[" node)]
      classmethod)

    :otherwise
    node))
