(ns goedel.utils.monad
  (:require [clojure.algo.monads :as monads]))


(defn update-val
  [k f & args]
  (monads/update-val k #(apply f % args)))
