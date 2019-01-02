(ns goedel.type-test
  (:require [goedel.type :as sut]
            [clojure.test :refer :all]))


(deftest alpha=-test
  (are [t1 t2] (sut/alpha= t1 t2)
    sut/integer sut/integer
    (sut/tuple sut/integer) (sut/tuple sut/integer)
    (sut/tuple sut/integer) (sut/tuple sut/integer)
    (-> (sut/tuple (sut/existential 1)) sut/integer)
    (-> (sut/tuple (sut/existential 0)) sut/integer)))
