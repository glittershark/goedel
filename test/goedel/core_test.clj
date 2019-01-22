(ns goedel.core-test
  (:require [clojure.core.logic :as l]
            [clojure.spec.alpha :as s]
            [clojure.test :refer :all]
            [clojure.test.check.generators :as gen]
            [com.gfredericks.test.chuck.clojure-test :refer [checking]]
            [com.gfredericks.test.chuck.generators :as gen']
            [goedel.core :as sut]
            [goedel.type :as t :refer [α=]]
            [goedel.type.refinement :as ref]))

(defmacro are-types [& exprs-and-types]
  `(are [x# ty#] (t/α= ty# (sut/type-infer (macroexpand x#)))
     ~@exprs-and-types))

(defn gen-simple-type []
  (gen/elements
   [t/integer
    t/string
    t/boolean
    t/float]))

(defn eta-abstract
  [[f & args]]
  {:post [(= (eval (cons f args))
             (eval %))]}
  (let [λ-args (map #(gensym (str "a" %)) (range (count args)))]
    `((fn [~@λ-args] (~f ~@λ-args)) ~@args)))

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
        t/float gen/double)]
   [x (ref/exact t x)]))

;;;

(deftest type-infer-test
  (testing "simple values"
    (checking "integers" 100 [i (s/gen integer?)]
      (is (α= (ref/exact t/integer i) (sut/type-infer i))))

    (checking "floats" 100 [f (s/gen float?)]
      (is (α= (ref/exact t/float f) (sut/type-infer f))))

    (testing "booleans"
      (are-types
       true (ref/exact t/boolean true)
       false (ref/exact t/boolean false)))

    (checking "keywords" 100 [kw (s/gen keyword?)]
      (is (α= (ref/exact t/keyword kw) (sut/type-infer kw)))))

  (testing "kind Type -> Type"
    (checking "vector of int" 100 [x (s/gen (s/coll-of integer? :kind vector?
                                                       :min-count 1))]
      (is (t/⊆ (sut/type-infer x)
               (t/vector-of t/integer))))

    (checking "vector of vector" 100
        [x (s/gen (s/coll-of (s/coll-of integer? :kind vector? :min-count 1)
                             :kind vector? :min-count 1))]
      (is (t/⊆ (sut/type-infer x)
               (t/vector-of (t/vector-of t/integer)))))

    (checking "heterogenous vector" 100
        [v1 (s/gen (s/coll-of integer?
                              :kind vector?
                              :min-count 1))
         v2 (s/gen (s/coll-of string?
                              :kind vector?
                              :min-count 1))
         :let [x (vec (concat v1 v2))]]
      (is (= (t/vector-of t/top) (sut/type-infer x)))))

  (testing "syntactic forms"
    (checking "do" 100 [xts (gen/list (exprs-with-types))
                        :when (seq xts)]
      (is (α= (-> xts last second)
              (sut/type-infer (macroexpand
                               `(do ~@(map first xts)))))
          "has the type of the last form"))

    (checking "let" 100 [[x t] (exprs-with-types)]
      (is (α= t (sut/type-infer (macroexpand `(let [x# ~x] x#))))))

    (checking "def" 100 [[x t] (exprs-with-types)]
      (is (α= t/var (sut/type-infer (macroexpand `(def ~'x ~x)))))
      (is (α= t (sut/type-infer (macroexpand `(do (def x# ~x)
                                                  x#))))))

    (testing "if"
      (testing "simple cases"
        (are-types
         `(if true 1 2) (ref/refine t/integer (ref/or #(l/== % 1)
                                                      #(l/== % 2)))
         `(if false 1 2) (ref/refine t/integer (ref/or #(l/== % 1)
                                                       #(l/== % 2)))))

      (testing "in a function"
        (is
         (α= (t/-> (t/tuple t/integer) t/integer)
             (sut/type-infer (macroexpand
                              `(fn [x#] (if true 1 x#))))))))

    (testing "java interop"
      (are-types
       (. clojure.lang.Numbers (inc 1)) (ref/exact t/integer 2)
       (clojure.lang.Numbers/inc 1) (ref/exact t/integer 2))))

  (testing "supertype unification"
    (is (α= (t/vector-of t/number)
            (sut/type-infer [1 1.0 2 2.0]))))

  (testing "simple functions"
    (is (α= (t/-> (t/tuple t/integer)
                  (t/vector-of t/integer))
            (sut/type-infer
             (macroexpand
              `(fn [x#]
                 [1 2 3 x#]))))))

  (testing "parametric functions"
    (is (α= (t/∀ [x] (t/-> (t/tuple x) x))
            (sut/type-infer (macroexpand `(fn [x#] x#))))))

  (testing "stdlib function calls"
    (are-types
     `(inc 1) t/integer
     `(inc 1.0) t/float
     `identity (t/∀ [x] (t/→ (t/tuple x) x)))

    (checking "eta-abstracted" 10 [eta-times gen/pos-int]
      (let [abstract-n-times (apply comp (repeat eta-times eta-abstract))]
        (are-types
         (abstract-n-times `(inc 1)) t/integer
         (abstract-n-times `(inc 1.0)) t/float)))))
