(ns goedel.type-test
  (:require [clojure.algo.monads :refer [domonad identity-m state-m with-monad
                                         update-state]]
            [clojure.test :refer :all]
            [goedel.type :as sut]
            [goedel.type.refinement :as ref]))

(deftest α=-test
  (are [t₁ t₂] (sut/α= t₁ t₂)
    sut/integer sut/integer
    (sut/tuple sut/integer) (sut/tuple sut/integer)
    (sut/tuple sut/integer) (sut/tuple sut/integer)
    (sut/tuple sut/integer (sut/existential 1))
    (sut/tuple sut/integer (sut/existential 0))))

(deftest ⊆-test
  (are [t₁ t₂] (sut/⊆ t₁ t₂)
    sut/integer sut/integer
    (ref/exact sut/integer 7) sut/integer
    (sut/vector-of (ref/exact sut/integer 7)) (sut/vector-of sut/integer)
    (sut/vector-of
     (sut/vector-of (ref/exact sut/integer 7))) (sut/vector-of
                                                 (sut/vector-of sut/integer))))

(deftest m-walk-test
  (with-monad identity-m
    (are [x y] (= x y)
      sut/integer               (sut/m-prewalk identity sut/integer)
      (sut/vector-of sut/float) (sut/m-prewalk #(if (= % sut/integer)
                                                  sut/float
                                                  %)
                                               (sut/vector-of sut/integer))))

  (with-monad state-m
    (are [expected actual] (= expected (actual 0))
      [sut/integer 1] (sut/m-prewalk (fn [t]
                                       (domonad
                                         [_ (update-state inc)]
                                         t))
                                     sut/integer))))
