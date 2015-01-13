(ns woa.apk.dex.asmdex.util
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
  ;; imports
  )

;;; declaration

;; var

;; func
(declare
 get-component-callback-method-all-external-invokes
 expand-invokes extract-dex-method-invokes
 comp-name-2-class-name class-name-2-comp-name)

;;; implementation

(defn get-component-callback-method-all-external-invokes
  "for each component callback method (i.e., on*), get its external invokes"
  [apk]
  (let [expanded-invokes (expand-invokes (extract-dex-method-invokes apk))]
    (into {}
          (map (fn [comp-type]
                 [comp-type
                  (into {}
                        (map (fn [comp-name]
                               [comp-name
                                (->> (get expanded-invokes
                                          ;; internal class name
                                          (comp-name-2-class-name comp-name))
                                     ;; filter event callbacks 
                                     (filter #(re-find #"^on[A-Z]"
                                                       (first %)))
                                     ;; filter external invokes
                                     (map (fn [[k methods]]
                                            [k
                                             (set (filter (fn [{:keys [class]}]
                                                            ;; external invokes
                                                            (not (get expanded-invokes
                                                                      class)))
                                                          methods))]))
                                     (into {}))])
                             (->> apk :manifest comp-type keys (map name))))])
               [:receiver :service :activity]))))


(defn expand-invokes
  "expand invokes to include transitive/indirect ones"
  [invokes]
  (let [expand (fn expand [method visited]
                 (if-let [method-invokes (get invokes method)]
                   ;; internal method - further expansion if not visited
                   (if-not (contains? visited method)
                     ;; not visited
                     (mapcat #(expand %
                                      (conj (set visited)
                                            method))
                             method-invokes)
                     ;; already visited - return method
                     #{method})
                   ;; external method - no further expansion
                   #{method}))]
    (let [result (atom {})
          tmp (->> invokes
                   (map (fn [[k v]]
                          [k (set (mapcat #(expand %
                                                   #{%})
                                          v))]))
                   (into {}))]
      (doseq [[{:keys [class method]} all-invokes] tmp]
        (swap! result assoc-in [class method] all-invokes))
      @result)))

(defn extract-dex-method-invokes
  "extract invokes in each method"
  [apk]
  (let [dex (:dex apk)]
    (->> (mapcat (fn [[class-name {:keys [methods]}]]
                   (map (fn [[method-name {:keys [code]}]]
                          {{:class class-name :method method-name}
                           (->> code
                                (filter #(= (:tag %)
                                            :method-insn))
                                (map #(do {:class (:owner %)
                                           :method (:name %)
                                           ;;:instruction (:instruction %)  ; not interesting to us
                                           }))
                                set)})
                        methods))
                 dex)
         (reduce merge))))

(defn comp-name-2-class-name
  "a.b.c -> La/b/c;"
  [comp-name]
  (str "L" (str/replace comp-name "." "/") ";"))

(defn class-name-2-comp-name
  "La/b/c; -> a.b.c"
  [class-name]
  (let [[_ class-name] (re-find #"^L([^;]+);$" class-name)]
    (str/replace class-name "/" ".")))








