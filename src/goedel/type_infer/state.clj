(ns goedel.type-infer.state
  (:refer-clojure :exclude [empty])
  (:require [clojure.algo.monads
             :refer
             [domonad fetch-val state-m update-state with-monad]]
            [goedel.utils.monad :refer [update-val]]
            [goedel.type :as t]))

(def empty
  {::exist-type-vars {}
   ::vars {}
   ::counter 0
   ::ns nil})

(with-monad state-m
  (defn new-exist-var []
    (domonad
      [counter (fetch-val ::counter)
       :let [var (t/existential counter)]
       _ (update-val ::counter inc)
       _ (update-val ::exist-type-vars assoc var nil)]
      var))

  (defn lookup-var [v]
    (domonad
      [vars (fetch-val ::vars)]
      (get vars v))))
