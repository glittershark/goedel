(ns goedel.core
  (:require [clojure.java.io :as io]
            [clojure.walk :as walk]
            [goedel.type-infer :refer [type-infer]])
  (:import java.io.PushbackReader))

(defn- read-file [filename]
  (with-open [f (PushbackReader. (io/reader filename))]
    (loop [res []]
      (let [expr (read {:eof ::eof} f)]
        (if (= expr ::eof)
          res
          (recur (conj res expr)))))))

(defn check-file [filename]
  (->> filename
       read-file
       (map walk/macroexpand-all)
       (map type-infer)
       dorun)
  true)

(comment
  (-> (read-file "/Users/griffin/code/goedel/src/goedel/core.clj")
      first
      walk/macroexpand-all
      goedel.type-infer/type-infer
      )

  clojure.lang.Var

  clojure.lang.Associative

  (filter #(= "pushThreadBindings" (.getName %))
          (.getMethods clojure.lang.Var))

  (.getMethods clojure.lang.Var)


  @goedel.type/--cls

  (= @goedel.type/--cls Void/TYPE)

  (class *1)


  in-ns
  )
