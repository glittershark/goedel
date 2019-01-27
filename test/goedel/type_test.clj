(ns goedel.type-test
  (:require [clojure.test :refer :all]
            [goedel.type :as sut]
            [goedel.type.refinement :as ref]))

(deftest α=-test
  (are [t₁ t₂] (sut/α= t₁ t₂)
    sut/integer sut/integer
    (sut/tuple sut/integer) (sut/tuple sut/integer)
    (sut/tuple sut/integer) (sut/tuple sut/integer)
    (sut/tuple sut/integer (sut/existential 1))
    (sut/tuple sut/integer (sut/existential 0)))

  (are [t1 t2] (not (sut/alpha= t1 t2))
    sut/integer sut/float
    (sut/tuple sut/integer) sut/float
    (sut/tuple sut/integer) (sut/tuple sut/float)
    (sut/tuple sut/integer) (sut/tuple (sut/existential 1))))

(deftest ⊆-test
  (are [t₁ t₂] (sut/⊆ t₁ t₂)
    sut/integer sut/integer
    (ref/exact sut/integer 7) sut/integer
    (sut/vector-of (ref/exact sut/integer 7)) (sut/vector-of sut/integer)
    (sut/vector-of
     (sut/vector-of (ref/exact sut/integer 7))) (sut/vector-of
                                                 (sut/vector-of sut/integer))))

(deftest prewalk-test
  (are [x y] (= x y)
    sut/integer               (sut/prewalk identity sut/integer)
    (sut/vector-of sut/float) (sut/prewalk #(if (= % sut/integer)
                                              sut/float
                                              %)
                                           (sut/vector-of sut/integer))))
