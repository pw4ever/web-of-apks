(ns woa.apk.dex.asmdex.parse
  ;; internal libs
  (:require [woa.apk.dex.parse
             :refer [the-dex]]
            [woa.apk.util
             :refer [get-apk-file-input-stream]]           
            [woa.apk.dex.asmdex.opcodes
             :refer [decode-opcode
                     encode-opcode]])  
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
  ;; http://asm.ow2.org/doc/tutorial-asmdex.html
  (:import (org.ow2.asmdex ApplicationReader
                           ApplicationVisitor
                           ClassVisitor
                           AnnotationVisitor
                           FieldVisitor
                           MethodVisitor
                           Opcodes)))

;;; declaration

(declare parse-the-dex-in-apk)

;;; implementation

(defn parse-the-dex-in-apk
  "parse the dex in apk"
  [apk & {:keys []
          :as args}]
  (let [api Opcodes/ASM4
        app-reader (ApplicationReader. api
                                       (get-apk-file-input-stream apk
                                                                  the-dex))
        the-structure (atom {})]
    (let [app-visitor (proxy [ApplicationVisitor] [api]
                        (visitClass [access name signature super-name interfaces]
                          (let [access (decode-opcode :access access)
                                signature (set signature)
                                interfaces (set interfaces)]
                            (swap! the-structure assoc-in [name]
                                   {:access access
                                    :name name
                                    :signature signature
                                    :super-name super-name
                                    :interfaces interfaces
                                    ;; placeholders
                                    :fields {}
                                    :methods {}})
                            (let [class-name name]
                              (proxy [ClassVisitor] [api]
                                (visitField [access name desc signature value]
                                  (let [access (decode-opcode :access access)
                                        signature (set signature)]
                                    (swap! the-structure assoc-in [class-name :fields name]
                                           {:access access
                                            :name name
                                            :desc desc
                                            :signature signature
                                            :value value})
                                    nil))
                                (visitMethod [access name desc signature exceptions]
                                  (let [access (decode-opcode :access access)
                                        signature (set signature)
                                        exceptions (set exceptions)
                                        ;; code to be appended here
                                        code (atom [])]
                                    (swap! the-structure assoc-in
                                           [class-name :methods name]
                                           {:access access
                                            :name name
                                            :desc desc
                                            :signature signature
                                            :exceptions exceptions
                                            ;; to be filled later at the visitEnd for MethodVisitor
                                            :code nil})
                                    (let [method-name name
                                          conj-code (fn [insn]
                                                      (swap! code conj insn))]
                                      (proxy [MethodVisitor] [api]
                                        (visitArrayLengthInsn [value-reg array-reg]
                                          (conj-code {:tag :array-length-insn
                                                      :instruction :array-length
                                                      :array array-reg
                                                      :value value-reg}))
                                        (visitArrayOperationInsn [opcode value-reg array-reg idx-reg]
                                          (conj-code {:tag :array-op-insn
                                                      :instruction (decode-opcode :instruction
                                                                                  opcode)
                                                      :array array-reg
                                                      :index idx-reg
                                                      :value value-reg}))
                                        (visitFieldInsn [opcode owner name desc value-reg obj-reg]
                                          (conj-code {:tag :field-insn
                                                      :instruction (decode-opcode :instruction
                                                                                  opcode)
                                                      :owner owner
                                                      :name name
                                                      :desc desc
                                                      :value value-reg
                                                      :object obj-reg}))
                                        (visitFillArrayDataInsn [array-reg array-data]
                                          (conj-code {:tag :fill-array-data-insn
                                                      :instruction :fill-array-data
                                                      :array array-reg
                                                      :data array-data}))
                                        (visitInsn [opcode]
                                          (conj-code {:tag :nullary-insn
                                                      :instruction (decode-opcode :instruction
                                                                                  opcode)}))
                                        (visitIntInsn [opcode reg]
                                          (conj-code {:tag :unary-insn
                                                      :instruction (decode-opcode :instruction
                                                                                  opcode)
                                                      :reg reg}))
                                        (visitJumpInsn [opcode label reg-a reg-b]
                                          (conj-code {:tag :jump-insn
                                                      :instruction (decode-opcode :instruction
                                                                                  opcode)
                                                      :label label
                                                      :reg-a reg-a
                                                      :reg-b reg-b}))
                                        (visitLabel [label]
                                          (conj-code {:tag :label
                                                      :label label}))
                                        (visitLineNumber [line start]
                                          (conj-code {:tag :line-number
                                                      :line line
                                                      :start start}))
                                        (visitLocalVariable [name desc signature start end index]
                                          (conj-code {:tag :local-variable
                                                      :name name
                                                      :desc desc
                                                      :signature signature
                                                      :start start
                                                      :end end
                                                      :index index}))
                                        (visitLookupSwitchInsn [reg default switch-keys labels]
                                          (let [switch-keys (vec switch-keys)
                                                labels (vec labels)]
                                            (conj-code {:tag :lookup-switch-insn
                                                        :instruction :lookup-switch
                                                        :reg reg
                                                        :default default
                                                        :switch-keys switch-keys
                                                        :labels labels})))
                                        (visitMaxs [max-stack _]
                                          ;; local vars + param vars (last ones; "this" implicit for instance method)
                                          (swap! the-structure assoc-in
                                                 [class-name :methods method-name :vars]
                                                 max-stack))
                                        (visitMethodInsn [opcode owner name desc arguments]
                                          (let [arguments (vec arguments)]
                                            (conj-code {:tag :method-insn
                                                        :instruction (decode-opcode :instruction
                                                                                    opcode)
                                                        :owner owner
                                                        :name name
                                                        :desc desc
                                                        :arguments arguments})))
                                        (visitMultiANewArrayInsn [desc regs]
                                          (let [regs (vec regs)]
                                            (conj-code {:tag :multi-a-newarray-insn
                                                        :instruction :multi-a-newarray
                                                        :desc desc
                                                        :reg regs})))
                                        (visitOperationInsn [opcode dest-reg src-reg-1 src-reg-2 value]
                                          (conj-code {:tag :op-insn
                                                      :instruction (decode-opcode :instruction
                                                                                  opcode)
                                                      :dest-reg dest-reg
                                                      :src-reg-1 src-reg-1
                                                      :src-reg-2 src-reg-2
                                                      :value value}))
                                        (visitParameters [params]
                                          (let [params (vec params)]
                                            (swap! the-structure assoc-in
                                                   [class-name :methods method-name :params]
                                                   params)))
                                        (visitStringInsn [opcode dest-reg string]
                                          (conj-code {:tag :string-insn
                                                      :instruction (decode-opcode :instruction
                                                                                  opcode)
                                                      :dest-reg dest-reg
                                                      :string string}))
                                        (visitTableSwitchInsn [reg min max default labels]
                                          (let [labels (vec labels)]
                                            (conj-code {:tag :table-switch-insn
                                                        :instruction :table-switch
                                                        :reg reg
                                                        :min min
                                                        :max max
                                                        :default default
                                                        :labels labels})))
                                        (visitTryCatchBlock [start end handler type]
                                          (conj-code {:tag :try-catch-block
                                                      :start start
                                                      :end end
                                                      :handler handler
                                                      :type type}))
                                        (visitTypeInsn [opcode dest-reg ref-reg size-reg type]
                                          (conj-code {:tag :type-insn
                                                      :instruction (decode-opcode :instruction
                                                                                  opcode)
                                                      :ref-reg ref-reg
                                                      :size-reg size-reg
                                                      :type type}))
                                        (visitVarInsn [opcode dest-reg var]
                                          (conj-code {:tag :var-insn
                                                      :instruction (decode-opcode :instruction
                                                                                  opcode)
                                                      :dest-reg dest-reg
                                                      :var var}))

                                        (visitEnd []
                                          ;; now save the code
                                          (swap! the-structure assoc-in
                                                 [class-name :methods method-name :code]
                                                 @code)))))))))))]
      (.accept app-reader
               app-visitor
               (bit-or 0
                       ApplicationReader/SKIP_DEBUG))
      @the-structure)))
