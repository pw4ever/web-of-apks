(ns woa.neo4j.recipe
  "recipes for queries"
  ;; common libs
  (:require [clojure.string :as str]
            [clojure.set :as set]
            [clojure.walk :as walk]
            [clojure.zip :as zip]
            [clojure.java.io :as io]
            [clojure.pprint :refer [pprint print-table]]
            [clojure.stacktrace :refer [print-stack-trace]]))

;;; declaration

(declare get-app-skeleton)

;;; implementation

(defn get-app-skeleton
  "get the skeleton of an app"
  [{:keys [sha256 package versionCode versionName]
    :as apk}
   &
   {:keys [return?]
    :as options}]
  (str/join " "
            [(format "MATCH (apk:Apk%1$s)"
                     (if apk
                       (format "{%1$s}"
                               (str/join ","
                                         (->> apk
                                              (map (fn [[k v]]
                                                     (str (name k) ":"
                                                          (format "\"%1$s\""
                                                                  v)))))))
                       ""))
             "OPTIONAL MATCH (signingKey:SigningKey)"
             "-[:SIGN]-> (apk)"
             "-[:CONTAIN]-> (dex:Dex)"
             "-[:CONTAIN]-> (class:Class)"
             "-[:CONTAIN]-> (callback:Callback)"
             "OPTIONAL MATCH (explicitInvoke) <-[:EXPLICIT_INVOKE]- (callback) -[:IMPLICIT_INVOKE]-> (implicitInvoke)"
             (if return?
               "RETURN signingKey, apk, dex, class, callback, explicitInvoke, implicitInvoke"
               "")]))

(defn get-app-by-class-complexity
  "sort apps by how many component classes they have"
  [&
   {:keys [skip limit desc where return?]
    :as options
    :or {limit 5}}]
  (str/join " "
            ["MATCH (apk:Apk)"
             "-[:CONTAIN]-> (:Dex)"
             "-[:CONTAIN]-> (class:Class)"
             "WITH apk, count(class) as cc"
             (if where (format "WHERE %1$s" where) "")
             (if return? "RETURN apk, cc" "")
             "ORDER BY cc"
             (if desc "DESC" "")
             (if limit (format "LIMIT %1$d" limit) "")
             (if skip (format "SKIP %1$d" skip) "")
             ]))

