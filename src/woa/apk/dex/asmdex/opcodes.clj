(ns woa.apk.dex.asmdex.opcodes
  ;; common libs
  (:require [clojure.string :as str]
            [clojure.set :as set]
            [clojure.walk :as walk]
            [clojure.zip :as zip]
            [clojure.java.io :as io]
            [clojure.pprint :refer [pprint print-table]]
            [clojure.stacktrace :refer [print-stack-trace]])  
  ;; special libs
  (:require [clojure.reflect :refer [reflect]])
  ;; imports
  (:import (org.ow2.asmdex Opcodes)))

(declare decode-opcode encode-opcode)

(let [opcode-map {:access "ACC_"
                  :debug "DBG_"
                  :instruction "INSN_"
                  :type "TYPE_"
                  :value "VALUE_"
                  :visibility "VISIBILITY_"}
      opcodes (into {}
                    (map (fn [[tag name-prefix]]
                           [tag
                            (into {}
                                  (->>  Opcodes
                                    reflect
                                    :members
                                    (map (comp str :name))
                                    (filter #(.startsWith % name-prefix))
                                    (map (fn [field-name]
                                           [(keyword (let [prettify-opcode-name
                                                           (fn [name]
                                                             (let [[_ name]
                                                                   (re-find #"^[^_]+_(.+)$" name)]
                                                               (-> name
                                                                 str/lower-case
                                                                 (str/replace "_" "-"))))]
                                                       (prettify-opcode-name field-name)))
                                            (eval `(. Opcodes
                                                      ~(symbol field-name)))]))))])
                         opcode-map))
      opcodes-invert (into {}
                           (map (fn [[tag opcodes]]
                                  [tag
                                   (set/map-invert opcodes)])
                                opcodes))]
  (defn- decode-ored-opcode
    "decode or-ed opcode from 'int' to 'set of keywords'"
    [opcode-type code]
    (let [opcode-type (keyword opcode-type)
          opcodes (opcode-type opcodes)]
      (set (filter #(not= 0
                          (bit-and code
                                   (get opcodes % 0)))
                   (keys opcodes)))))
  
  (defn- encode-ored-opcode
    "encode or-ed opcode from 'seq of keywords' to 'int'"
    [opcode-type code]
    (let [opcode-type (keyword opcode-type)
          opcodes (opcode-type opcodes)]
      (reduce bit-or 0
              (map opcodes
                   (set/intersection (set code)
                                     (set (keys opcodes)))))))

  (defn- decode-exclusive-opcode
    "deocde exclusive opcode from 'int' to 'keyword'"
    [opcode-type code]
    (get ((keyword opcode-type) opcodes-invert)
         code))

  (defn- encode-exclusive-opcode
    "encode exclusive opcode from 'keyword' to 'int'"
    [opcode-type code]
    (get ((keyword opcode-type) opcodes)
         code))

  (let [impl {:encode {:ored encode-ored-opcode
                       :exclusive encode-exclusive-opcode}
              :decode {:ored decode-ored-opcode
                       :exclusive decode-exclusive-opcode}}
        opcode-type-map {:access :ored
                         :debug :exclusive
                         :instruction :exclusive
                         :type :exclusive
                         :value :exclusive
                         :visibility :exclusive}]

    (defn- do-opcode
      "do encode/decode on opcode"
      [dowhat opcode-type code]
      (let [dowhat (keyword dowhat)
            opcode-type (keyword opcode-type)]
        ((get (dowhat impl)
              (opcode-type opcode-type-map))
         opcode-type code)))

    
    (defn decode-opcode
      "decode opcode"
      [opcode-type code]
      (do-opcode :decode opcode-type code))

    (defn encode-opcode
      "encode opcode"
      [opcode-type code]
      (do-opcode :encode opcode-type code))))
