(ns goedel.core-test
  (:require [clojure.spec.alpha :as s]
            [clojure.test :refer :all]
            [clojure.test.check.generators :as gen]
            [com.gfredericks.test.chuck.generators :as gen']
            [com.gfredericks.test.chuck.clojure-test :refer [checking]]
            [goedel.core :as sut]
            [goedel.type :as t]))

(defmacro are-types [& exprs-and-types]
  `(are [x# ty#] (= ty# (sut/type-infer (macroexpand x#)))
     ~@exprs-and-types))

(defn gen-simple-type []
  (gen/elements
   [t/integer
    t/string
    t/boolean
    t/float]))

(defn exprs-with-types
  "Generator for a two-tuple of an expression and its type,
   ∀ {T : Type} → (a : T) × T"
  []
  (gen'/for
   [t (gen-simple-type)
    x (condp = t
        t/integer gen/int
        t/string gen/string
        t/boolean gen/boolean
        t/float gen/double)
    ]
   [x t]))

;;;

(deftest type-infer-test
  (testing "simple values"
    (checking "integers" 100 [i (s/gen integer?)]
      (is (= t/integer (sut/type-infer i))))

    (checking "floats" 100 [i (s/gen float?)]
      (is (= t/float (sut/type-infer i))))

    (testing "booleans"
      (are-types
       true t/boolean
       false t/boolean)))

  (testing "kind Type -> Type"
    (checking "vector of int" 100 [x (s/gen (s/coll-of integer? :kind vector?
                                                       :min-count 1))]
      (is (= (t/vector-of t/integer) (sut/type-infer x))))

    (checking "vector of vector" 100
        [x (s/gen (s/coll-of (s/coll-of integer? :kind vector? :min-count 1)
                             :kind vector? :min-count 1))]
        (is (= (t/vector-of (t/vector-of t/integer)) (sut/type-infer x))))

    (checking "heterogenous vector" 100
        [v1 (s/gen (s/coll-of integer?
                              :kind vector?
                              :min-count 1))
         v2 (s/gen (s/coll-of string?
                              :kind vector?
                              :min-count 1))
         :let [x (into [] (concat v1 v2))]]
        (is (= (t/vector-of t/bot) (sut/type-infer x)))))

  (testing "syntactic forms"
    (checking "do" 100 [xts (gen/list (exprs-with-types))
                        :when (< 0 (count xts))]
      (is (= (-> xts last second)
             (sut/type-infer (macroexpand
                              `(do ~@(map first xts)))))
          "has the type of the last form"))

    (checking "let" 100 [[x t] (exprs-with-types)]
      (is (= t (sut/type-infer (macroexpand `(let [x# ~x] x#))))))

    (checking "def" 100 [[x t] (exprs-with-types)]
      (is (= t/var (sut/type-infer (macroexpand `(def ~'x ~x)))))
      (is (= t (sut/type-infer (macroexpand `(do (def x# ~x)
                                                 x#))))))

    (testing "java interop"
      (are-types
       (. clojure.lang.Numbers (inc 1)) t/integer
       (clojure.lang.Numbers/inc 1) t/integer)))

  (testing "simple functions"
    (is (= (t/-> (t/tuple t/integer)
                 (t/vector-of t/integer))
           (sut/type-infer
            (macroexpand
             `(fn [x#]
                [1 2 3 x#]))))))

  (testing "stdlib function calls"
    (are-types
     `(inc 1) t/integer
     `(inc 1.0) t/float)))
