(ns goedel.type
  (:refer-clojure :exclude [type vector-of boolean float -> * class])
  (:require [clojure.core :as c]
            [clojure.spec.alpha :as s]
            [clojure.walk :as walk]
            [goedel.protocols :as p]
            [clojure.set :as set]))

;;;

(def top
  ^{`s/specize* #(s/spec any?)
    `p/as-java-class (fn [_] Object)}
  {::type ::top})

(def bot
  ^{`s/specize* #(s/spec any?)}
  {::type ::bot})

(def integer
  ^{`s/specize* #(s/spec integer?)
    `p/as-java-class (fn [_] Long/TYPE)}
  {::type ::integer})

(def string
  ^{`s/specize* #(s/spec string?)}
  {::type ::string})

(def boolean
  ^{`s/specize* #(s/spec boolean?)}
  {::type ::boolean})

(def float
  ^{`s/specize* #(s/spec float?)
    `p/as-java-class (fn [_] Double/TYPE)}
  {::type ::float})

(def var
  ^{`s/specize* #(s/spec var?)
    `p/as-java-class clojure.lang.Var}
  {::type ::var})

(defn vector-of [t]
  ^{`s/specize* #(s/coll-of t :kind vector?)}
  {::type ::vector-of
   ::type-args [t]})

(defn seq-of [t]
  ^{`s/specize* #(s/coll-of t)}
  {::type ::seq-of
   ::type-args [t]})

(defn -> [t1 t2]
  ^{`s/specize* #(s/fspec :args t1 :ret t2)}
  {::type ::->
   ::type-args [t1 t2]})

(defn * [t]
  ^{`s/specize* #(s/* t)}
  (seq-of t))

(defn types* [tys]
  ;; NOTE should this be somethign other than a vector? does it matter?
  ^{`s/specize* #(s/tuple-impl tys tys)}
  {::type ::heterogenous-sequence
   ::type-args tys})

(defn tuple [& tys]
  (types* tys))

(defn dependent [arg-vars f]
  {::type ::dependent
   ::dependent-args arg-vars
   ::dependent-fn f})

(defn class [cls]
  {::type ::class
   ::type-args [cls]})

(defn existential [n]
  {::existential n})

;;;

(defn class->type [cls]
  (condp = cls
    Long/TYPE integer
    Double/TYPE float))

(defn return-type [function-type]
  (assert (= ::-> (::type function-type)))
  (c/-> function-type ::type-args last))

(defn existential? [t]
  (::existential t))

(defn universal? [t]
  (::universal t))

(def type-var? (some-fn existential? universal?))

(defn existential->universal [t]
  (set/rename-keys t {::existential ::universal}))

(defn universal->existential [t]
  (set/rename-keys t {::universal ::existential}))

(defn universalize [t]
  (walk/prewalk
   (fn [x]
     (if (existential? x)
       (set/rename-keys x {::existential ::universal})
       x))
   t))

(comment
  (universalize (existential 1))
  )
