(ns goedel.type
  (:refer-clojure
   :exclude
   [type vector-of boolean float -> * class deftype < parents keyword
    symbol])
  (:require [clojure.core :as c]
            [clojure.core.logic :as l]
            [clojure.set :as set]
            [clojure.spec.alpha :as s]
            [clojure.walk :as walk]
            [goedel.protocols :as p]
            [goedel.type.lattice :as lattice]
            [goedel.type.refinement :as ref]
            [ubergraph.core :as uber]))

(s/def ::inherits ident?)
(s/def ::deftype-args
  (s/cat :name simple-symbol?
         :args (s/? (s/coll-of simple-symbol? :kind vector?))
         :meta (s/? map?)
         :options (s/keys* :opt-un [::inherits])
         :protocol-impls (s/* any?)))

(declare inherit!)
(defmacro deftype
  {:arglists '([name ?args ?meta & protocol-impls])}
  [& args]
  (let [{:keys [name args meta protocol-impls]
         {:keys [inherits]} :options} (s/conform ::deftype-args args)

        kw-name (c/keyword "goedel.type" (c/name name))
        protocol-meta
        (into {}
              (map (fn [[fname [this-arg & fn-args] & fn-body]]
                     (let [qualified-fname
                           (c/symbol (c/-> *ns*
                                           ns-aliases
                                           (get (c/symbol (c/namespace fname)))
                                           ns-name
                                           c/name)
                                     (c/name fname))]
                       [`(quote ~qualified-fname)
                        `(fn [~this-arg ~@fn-args]
                           ~@(if args
                               [`(let [~args (::type-args ~this-arg)]
                                   ~@fn-body)]
                               fn-body))])))
              protocol-impls)]
    `(do
       ~(if args
          `(defn ~name ~@(when meta [meta]) ~args
             (with-meta
               {::type ~kw-name
                ::type-args ~args}
               ~protocol-meta))
          `(do (def ~name
                 (with-meta
                   {::type ~kw-name}
                   ~protocol-meta))
               ~@(when meta [`(alter-meta! #'~name merge ~meta)])))
       ~@(when inherits
           [`(inherit! ~name (let [inherits# ~inherits]
                               (if (keyword? inherits#)
                                 {::type inherits#}
                                 inherits#)))]))))

;;;

(deftype top
  (s/specize* [_] (s/spec any?))
  (p/as-java-class [_] Object))

(deftype bot
  (s/specize* [_] (s/spec (constantly false)))
  (p/as-java-class [_] nil))

(extend-protocol p/Type
  Object
  (parents [_] [top])
  (children [_] [bot]))

;;;

(def ^:dynamic *hierarchy* (atom (uber/digraph)))

(defn inherit! [t1 t2]
  (swap! *hierarchy* uber/add-directed-edges [(::type t1) (::type t2)]))

(defn parents [t]
  (if (= t top) #{}
      (into #{top}
            (concat (p/parents t)
                    (when (contains? t ::ref/refinement)
                      [(dissoc t ::ref/refinement)])))))

(defn children [t]
  (if (= t bot) #{} (into #{bot} (p/children t))))

(def lattice
  (reify lattice/BasicDigraph
    (successors [_ {::keys [type] :as t}]
      (into (map (fn [ty] {::type ty})
                 (lattice/successors @*hierarchy* type))
            (parents t)))
    (predecessors [_ {::keys [type] :as t}]
      (into (map (fn [ty] {::type ty})
                 (lattice/predecessors @*hierarchy* type))
            (children t)))))

(defn sup [t₁ t₂]
  (or (lattice/sup lattice t₁ t₂) top))

(defn sub [t₁ t₂]
  (or (lattice/sup lattice t₁ t₂) bot))

;;;

(deftype number
  (s/specize* [_] (s/spec number?))
  (p/as-java-class [_] Number))

(deftype integer
  :inherits number
  (s/specize* [_] (s/spec integer?))
  (p/as-java-class [_] Long/TYPE))

(deftype float
  :inherits number
  (s/specize* [_] (s/spec float?))
  (p/as-java-class [_] Double/TYPE))

(def string
  ^{`s/specize* #(s/spec string?)}
  {::type ::string})

(def boolean
  ^{`s/specize* #(s/spec boolean?)}
  {::type ::boolean})

(deftype keyword
  (s/specize* [_] (s/spec keyword?))
  (p/as-java-class [_] clojure.lang.Keyword))

(deftype symbol
  (s/specize* [_] (s/spec symbol?))
  (p/as-java-class [_] clojure.lang.Symbol))

(def var
  ^{`s/specize* #(s/spec var?)
    `p/as-java-class clojure.lang.Var}
  {::type ::var})

(deftype namespace
  (s/specize* [_] (s/spec #(instance? clojure.lang.Namespace %)))
  (p/as-java-class [_] clojure.lang.Namespace))

(defn seq-of [t]
  ^{`s/specize* #(s/coll-of t)}
  {::type ::seq-of
   ::type-args [t]})

(deftype vector-of [t]
  :inherits seq-of
  (s/specize* [_] (s/coll-of t :kind vector?))
  (p/as-java-class [_] clojure.lang.PersistentVector))

(deftype map-of [kt vt]
  :inherits seq-of
  (s/specize* [_] (s/map-of kt vt :kind vector?))
  (p/as-java-class [_] clojure.lang.PersistentHashMap))

(comment
  (s/conform ::deftype-args
             (list ['t]
                   :inherits 'seq-of
                   '(s/specize* #(s/coll-of t :kind vector?))))
  )

(defn -> [t1 t2]
  ^{`s/specize* #(s/fspec :args t1 :ret t2)}
  {::type ::->
   ::type-args [t1 t2]})

(def → ->)

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

(defn dependent? [t] (= ::dependent (::type t)))

(defn class [cls]
  {::type ::class
   ::type-args [cls]})

(defn existential [n]
  {::existential n})

(defn universal [n]
  {::universal n})

;;;

(defn class->type [cls]
  (condp = cls
    Long/TYPE integer
    Double/TYPE float
    Void/TYPE bot))

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

(defn walk [inner outer type]
  (let
      [itas (when-let [type-args (::type-args type)]
              (map inner type-args))]
    (outer (if itas (assoc type ::type-args (vec itas)) type))))

(defn prewalk [f type]
  (walk (partial prewalk f) identity (f type)))


(defmacro forall [tvs typ]
  `(let [~@(->> tvs
                (map-indexed vector)
                (mapcat (fn [[idx vname]]
                          [vname `(universal ~idx)])))]
     ~typ))

(defmacro ∀ [tvs typ]
  `(forall ~tvs ~typ))

(defmacro exists [tvs typ]
  `(let [~@(->> tvs
                (map-indexed vector)
                (mapcat (fn [[idx vname]]
                          [vname `(universal ~idx)])))]
     ~typ))

(defmacro ∃ [tvs typ]
  `(exists ~tvs ~typ))

(defn alpha= [t₁ t₂]
  (or
   (and (existential? t₁) (existential? t₂))
   (and (universal? t₁) (universal? t₂))
   (and (= (::type t₁)
           (::type t₂))
        (ref/intersect? (::ref/refinement t₁)
                        (::ref/refinement t₂))
        (every? identity (map alpha=
                              (::type-args t₁)
                              (::type-args t₂))))))

(def α= alpha=)

(defn ⊆ [t₁ t₂]
  (or (α= t₁ t₂)
      (and (= (::type t₁) (::type t₁))
           (= (count (::type-args t₁))
              (count (::type-args t₂)))
           (ref/intersect? (::ref/refinement t₁)
                           (::ref/refinement t₂))
           (every? some? (map ⊆
                          (::type-args t₁)
                          (::type-args t₂))))
      (when-let [ps (seq (parents t₁))]
        (some #(⊆ % t₂) ps))))
