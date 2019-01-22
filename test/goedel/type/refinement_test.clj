(ns goedel.type.refinement-test
  (:require [clojure.core.logic :as l]
            [clojure.test :refer :all]
            [goedel.type.refinement :as sut]))

(deftest intersect? test
  (are [r₁ r₂] (sut/intersect? r₁ r₂)
    #(l/== % 1) #(l/== % 1)
    #(l/membero % [1 2]) #(l/membero % [2 3])
    #(l/membero % [1 2]) #(l/membero % [1 2]))

  (are [r₁ r₂] (not (sut/intersect? r₁ r₂))
    #(l/== % 1) #(l/== % 2)
    #(l/== % 1) #(l/membero % [2 3])
    #(l/membero % [1 2]) #(l/membero % [3 4])))
