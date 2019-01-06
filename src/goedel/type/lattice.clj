(ns goedel.type.lattice
  (:require [clojure.set :as set]
            [clojure.template :refer [do-template]]
            [goedel.type :as t]
            [ubergraph.alg :as alg]
            [ubergraph.core :as uber])
  (:import ubergraph.core.Ubergraph))

(defprotocol BasicDigraph
  (successors [this node])
  (predecessors [this node]))

(extend Ubergraph
  BasicDigraph
  {:successors uber/successors
   :predecessors uber/predecessors})

(do-template
 [f rel]
 (defn f [g n1 n2]
   (loop [left  #{n1}
          right #{n2}]
     (let [inter (set/intersection left right)]
       (case (count inter)
         1 (first inter)
         0 (let [next-left  (into left (mapcat (partial rel g) left))
                 next-right (into right (mapcat (partial rel g) right))]
             (when-not (or (empty? next-left)
                           (empty? next-right))
               (recur next-left next-right)))
         (throw (ex-info "non-unique parent of two items"
                         {:nodes   [n1 n2]
                          :graph   g
                          :parents inter}))))))

 sup successors
 sub predecessors)

(def ∧ sup)
(def ∨ sub)

;;; https://cs.stackexchange.com/a/89949
(defn lattice? [g]
  (and (alg/dag? g)
       (let [nodes (alg/topsort g)]
         (every?
          some?
          (for [n₁ nodes
                n₂ nodes]
            (try (and (∧ g n₁ n₂)
                      (∨ g n₁ n₂))
                 (catch RuntimeException e false)))))))
