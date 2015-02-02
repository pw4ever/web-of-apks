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
            [clojure.stacktrace :refer [print-stack-trace]]))

;;; declaration

;;; implementation

(defprotocol Sexp)

(defrecord ErrorSexp [type info]
  Sexp)

(defn make-error-sexp
  [type info]
  (ErrorSexp. type info))

(defrecord ExternalSexp [type info]
  Sexp)

(defn make-external-sexp
  [type info]
  (ExternalSexp. type info))

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
    (get-soot-class (:method this)))
  (get-soot-class-name [this]
    (get-soot-class-name (:method this)))
  (get-soot-name [this]
    (get-soot-name [this])))

(defn make-invoke-sexp
  [invoke-type method base args]
  (InvokeSexp. invoke-type method base args))

(defrecord InstanceSexp [class instance]
  Sexp
  SootQuery
  (get-soot-class [this]
    (get-soot-class (:class this)))
  (get-soot-class-name [this]
    (get-soot-class-name (:class this))))

(defn make-instance-sexp
  [class instance]
  (InstanceSexp. class instance))

(defrecord ClassSexp [class]
  Sexp
  SootQuery
  (get-soot-class [this]
    (get-soot-class (:class this)))
  (get-soot-class-name [this]
    (get-soot-class-name (:class this))))

(defn make-class-sexp
  [class]
  (ClassSexp. class))

(defrecord MethodSexp [instance method]
  Sexp
  SootQuery
  (get-soot-class [this]
    (get-soot-class (:instance this)))
  (get-soot-class-name [this]
    (get-soot-class-name (:instance this)))
  (get-soot-name [this]
    (get-soot-name (:method this))))

(defn make-method-sexp
  [instance method]
  (MethodSexp. instance method))

(defrecord FieldSexp [instance field]
  Sexp
  SootQuery
  (get-soot-class [this]
    (get-soot-class (:instance this)))
  (get-soot-class-name [this]
    (get-soot-class-name (:instance this)))
  (get-soot-name [this]
    (get-soot-name (:field this))))

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
