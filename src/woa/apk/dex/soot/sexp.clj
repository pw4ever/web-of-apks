(ns woa.apk.dex.soot.sexp
  "define symbolic expression (sexp)"
  ;; internal libs
  (:use woa.apk.dex.soot.util)
  ;; common libs
  (:require [clojure.string :as str]
            [clojure.set :as set]
            [clojure.walk :as walk]
            [clojure.zip :as zip]
            [clojure.java.io :as io]
            [clojure.pprint :refer [pprint print-table]]
            [clojure.stacktrace :refer [print-stack-trace]])
  (:import (clojure.lang IHashEq)))

;;; declaration

;;; implementation

(defprotocol Sexp)

(defrecord ErrorSexp [type info]
  Sexp)

(defn make-error-sexp
  [type info]
  (ErrorSexp. type info))

(defrecord ExternalSexp [type]
  Sexp)

(defn make-external-sexp
  [type]
  (ExternalSexp. type))

(defrecord BinaryOperationSexp [operator operands]
  Sexp)

(defn make-binary-operator-sexp
  [operator operands]
  (BinaryOperationSexp. operator operands))

(defrecord UnaryOperationSexp [operator operands]
  Sexp)

(defn make-unary-operator-sexp
  [operator operands]
  (UnaryOperationSexp. operator operands))

(defrecord InvokeSexp [invoke-type method base args]
  Sexp
  SootQuery
  (get-soot-class [this]
    (case invoke-type
      :static-invoke (->> (:method this) get-soot-class)
      (try
        (->> (:base this) get-soot-class)
        (catch Exception e
          (->> (:method this) get-soot-class)))))
  (get-soot-class-name [this]
    (->> this get-soot-class get-soot-name))
  (get-soot-name [this]
    (->> (:method this) get-soot-name))
  (soot-resolve [this]
    (->> (:method this) soot-resolve)))

(defn make-invoke-sexp
  [invoke-type method base args]
  (InvokeSexp. invoke-type method base args))

(defrecord InstanceSexp [class instance]
  Sexp
  Object
  SootQuery
  (get-soot-class [this]
    (->> (:class this) get-soot-class))
  (get-soot-class-name [this]
    (->> this get-soot-class get-soot-name))
  (get-soot-name [this]
    (->> this get-soot-class-name))
  (soot-resolve [this]
    (->> this get-soot-class soot-resolve)))

(defn make-instance-sexp
  [class instance]
  (InstanceSexp. class instance))

(defrecord ClassSexp [class]
  Sexp
  Object
  SootQuery
  (get-soot-class [this]
    (->> (:class this) get-soot-class))
  (get-soot-class-name [this]
    (->> this get-soot-class get-soot-name))
  (get-soot-name [this]
    (->> this get-soot-class-name))
  (soot-resolve [this]
    (->> this get-soot-class soot-resolve)))

(defn make-class-sexp
  [class]
  (ClassSexp. class))

(defrecord MethodSexp [instance method]
  Sexp
  SootQuery
  (get-soot-class [this]
    (->> (:instance this) get-soot-class))
  (get-soot-class-name [this]
    (->> this get-soot-class get-soot-name))
  (get-soot-name [this]
    (->> (:method this) get-soot-name))
  (soot-resolve [this]
    (->> (:method this) soot-resolve)))

(defn make-method-sexp
  [instance method]
  (MethodSexp. instance method))

(defrecord FieldSexp [instance field]
  Sexp
  SootQuery
  (get-soot-class [this]
    (->> (:instance this) get-soot-class))
  (get-soot-class-name [this]
    (->> this get-soot-class get-soot-name))
  (get-soot-name [this]
    (->> (:field this) get-soot-name))
  (soot-resolve [this]
    (->> (:field this) soot-resolve)))

(defn make-field-sexp
  [instance field]
  (FieldSexp. instance field))

(defrecord LocalSexp [local]
  Sexp)

(defn make-local-sexp
  [local]
  (LocalSexp. local))

(defrecord InstanceOfSexp [class instance]
  Sexp)

(defn make-instance-of-sexp
  [class instance]
  (InstanceOfSexp. class instance))

(defrecord NewArraySexp [base-type size]
  Sexp)

(defn make-new-array-sexp
  [base-type size]
  (NewArraySexp. base-type size))

(defrecord NewMultiArraySexp [base-type sizes]
  Sexp)

(defn make-new-multi-array-sexp
  [base-type sizes]
  (NewMultiArraySexp. base-type sizes))

(defrecord ArrayRefSexp [base index]
  Sexp)

(defn make-array-ref-sexp
  [base index]
  (ArrayRefSexp. base index))

(defrecord ConstantSexp [const]
  Sexp)

(defn make-constant-sexp
  [const]
  (ConstantSexp. const))

(defrecord CastSexp [value cast-type]
  Sexp)

(defn make-cast-sexp
  [value cast-type]
  (CastSexp. value cast-type))
