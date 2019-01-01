(ns goedel.core
  (:require [clojure.algo.monads
             :refer
             [defmonadfn
              domonad
              fetch-state
              fetch-val
              m-bind
              m-chain
              m-result
              m-seq
              set-state
              set-val
              state-m
              update-state
              with-monad]]
            [clojure.core.match :refer [match]]
            [clojure.datafy :refer [datafy]]
            [clojure.repl :as repl]
            [clojure.spec.alpha :as s]
            [clojure.walk :as walk]
            [goedel.protocols :as p]
            [goedel.type :as t]
            [goedel.type-infer.state :as state]
            [goedel.utils.monad :refer [update-val]]))

(def special-form?
  #{`let*
    `do
    'clojure.core/def
    'def
    `fn
    `fn*
    '.})

(defn- invocation? [expr]
  (or (instance? clojure.lang.Cons expr)
      (instance? clojure.lang.PersistentList expr)))

(defn- sf-invoke? [expr]
  (and (invocation? expr)
       (special-form? (first expr))))

(defn- function-call? [expr]
  (and (invocation? expr)
       (not (special-form? (first expr)))))

(defn- local-var-symbol? [s]
  (and (simple-symbol? s)
       (not-any? #{\.} (name s))))

(defn- class-symbol? [s]
  (and (simple-symbol? s)
       (some #{\.} (name s))))

;;;

(defmonadfn m-reduce
  ([f xs]
   (match [xs]
     [([] :seq)] (f)
     [([x] :seq)] (m-result x)
     [([x1 x2 & xs*] :seq)] (domonad
                              [x (f x1 x2)
                               r (m-reduce f (cons x xs*))]
                              r)))
  ([f v xs]
   (match [xs]
     [([] :seq)] (m-result v)
     [([x & xs*] :seq)] (domonad
                          [x′ (f v x)
                           r (m-reduce f x′ xs)]
                          r))))

(defmonadfn m-map
  ([f coll]
   (m-seq (map f coll)))
  ([f coll & colls]
   (m-seq (apply map f coll colls))))

(defmonadfn m-walk
  [inner outer form]
  (cond
   (list? form)
   (domonad
     [iforms (m-map inner form)
      ilist (apply list iforms)
      r (outer ilist)]
     r)

   (instance? clojure.lang.IMapEntry form)
   (domonad
     [ik (inner (key form))
      iv (inner (val form))
      r (outer (clojure.lang.MapEntry/create ik iv))]
     r)

   (seq? form)
   (domonad
     [iforms (m-map inner form)
      r (outer (doall iforms))]
     r)

   (instance? clojure.lang.IRecord form)
   (domonad
     [ir (m-reduce (fn [r x] (domonad [ix (inner x)] (conj r ix)))
                   form form)
      r (outer ir)]
     r)

   (coll? form)
   (domonad
     [iforms (m-map inner form)
      r (outer (into (empty form) iforms))]
     r)

   :else (outer form)))

(defmonadfn m-postwalk
  [f form]
  (m-walk (partial m-postwalk f) f form))

(defmonadfn m-prewalk
  [f form]
  (domonad
    [fform (f form)
     r (m-walk (partial m-prewalk f) m-result fform)]
    r))

;;;

(defn source [f]
  (-> f
      repl/source-fn
      read-string
      macroexpand))

;;;

(with-monad state-m

  (defn sub [t1 t2]
    (m-result (if (= t1 t2) t1 t/bot)))

  (defn sup [t1 t2]
    (m-result (if (= t1 t2) t1 t/top)))

  (defn <unify
    "unify covariantly up the lattice"
    ([] (m-result t/bot))
    ([t1] t1)
    ([t1 t2]
     (cond
       (= t1 t/top) (m-result t/top)
       (= t1 t2) (m-result t2)
       (t/type-var? t1) (domonad
                          [_ (update-val ::state/vars assoc t1 t2)]
                          t2)
       (t/type-var? t2) (<unify t2 t1)
       (and (= (::t/type t1) (::t/type t2))
            (= (count (::t/type-args t1))
               (count (::t/type-args t2))))
       (domonad
         [args (m-map <unify (::t/type-args t1) (::t/type-args t2))]
         (assoc t1 ::t/type-args args))
       :else (sub t1 t2))))

  (defn >unify
    "unify contravariantly down the lattice"
    ([] t/top)
    ([t1] t1)
    ([t1 t2]
     (cond
       (= t1 t/top) t2
       (= t1 t2) t2
       :else (throw (ex-info "Could not unify"
                             {:types [t1 t2]})))))

  (declare type-infer*)

  (defn ti-method-invoke [obj m args]
    (domonad
      [obj-t (type-infer* obj)
       arg-ts (m-map type-infer* args)
       r
       (letfn
           [(go
              [obj-t m arg-ts]
              (if-let [existentials (->> arg-ts
                                         (cons obj-t)
                                         (filter t/existential?)
                                         seq)]
                (m-result
                 (t/dependent
                  existentials
                  (fn [existential-type-map]
                    (let [obj-t* (if (t/existential? obj-t)
                                   (get existential-type-map obj)
                                   obj-t)
                          arg-ts* (replace existential-type-map arg-ts)]
                      ;; this'll be fun
                      ;; hope it halts!
                      (go obj-t* m arg-ts*)))) )
                (loop [obj-t obj-t]
                  (cond
                    (class? obj-t)
                    (do
                      (-> obj-t
                          (.getMethod
                           (name m)
                           (into-array Class (map p/as-java-class arg-ts)))
                          .getReturnType
                          t/class->type
                          m-result))
                    (class-symbol? obj-t)
                    (recur (resolve obj-t))
                    (= ::t/class (::t/type obj-t))
                    (recur (-> obj-t ::t/type-args first))
                    (nil? obj-t)
                    (throw (NullPointerException.))
                    :else
                    (recur (class obj-t))))))]
           (go obj-t m arg-ts))]
      r))

  (defn ti-special-form [expr]
    (match [expr]
      [([`let* vars & body] :seq)]
      (domonad
        [vs (m-map (fn [[v x]]
                     (domonad
                       [t (type-infer* x)
                        _ (update-val ::state/vars assoc v t)]
                       v))
                   (partition 2 vars))
         res (type-infer* `(do ~@body))
         _ (m-map (fn [v] (update-val ::state/vars dissoc v)) vs)]
        res)

      [([`do & body] :seq)]
      (domonad
        [ts (m-map type-infer* body)]
        (last ts))

      [([(:or 'clojure.core/def 'def) n v] :seq)]
      (domonad
        [t (type-infer* v)
         ns* (fetch-val ::state/ns)
         _ (update-val ::state/vars assoc
                       (symbol (some-> ns* ns-name name) (name n))
                       t)]
        t/var)

      [([(:or 'clojure.core/fn 'fn `fn*) & args] :seq)]
      ;; TODO handle multiple arities
      (let [[[vars & body]] (if ((some-fn list?
                                          #(instance? clojure.lang.Cons %))
                                 (first args))
                              args
                              [args])]
        (domonad
          [arg-vars (m-map (fn [v]
                             (domonad
                               [tv (state/new-exist-var)
                                _ (update-val ::state/vars assoc v tv)]
                               tv))
                           vars)
           st (fetch-state)
           res (type-infer* `(do ~@body))
           arg-tys (m-map #(domonad [t (state/lookup-var %)] (or t %)) arg-vars)
           _ (m-map (fn [v] (update-val ::state/vars dissoc v)) arg-vars)]
          (t/universalize
           (t/-> (t/types* arg-tys) res))))

      [([`. obj ([m & args] :seq)] :seq)]
      (ti-method-invoke obj m args)))


  (defn instantiate-dependent [{::t/keys [dependent-args dependent-fn]} vs]
    (dependent-fn
     (into {}
           (map (fn [[k v]] [(t/universal->existential k) v]))
           (select-keys vs dependent-args))))

  (defn subs-universals [t vs]
    (m-prewalk
     (fn [x]
       (cond
         (and (t/universal? x) (contains? vs x)) (m-result (get vs x))
         (= ::t/dependent (::t/type x)) (instantiate-dependent x vs)
         :else (m-result x)))
     t))

  (defn ti-function-call [[f & args]]
    (domonad
      [arg-tys (m-map type-infer* args)
       ft (type-infer* f)
       rv (state/new-exist-var)
       ft* (<unify ft (t/-> (t/types* arg-tys) rv))
       vs (fetch-val ::state/vars)
       ft** (subs-universals ft* vs)]
      (t/return-type ft**)))

  (defn lookup-and-type-infer [s]
    (let [src (source s)]
      (domonad
        [old-ns (fetch-val ::state/ns)
         _ (set-val ::state/ns (-> s namespace symbol the-ns))
         r (type-infer* src)
         _ (set-val ::state/ns old-ns)]
        r)))

  (defn ti-qualified-symbol [s]
    (domonad
      [t (state/lookup-var s)
       t (if t
           (m-result t)
           (domonad
             [r (lookup-and-type-infer s)
              st (fetch-state)
              t (state/lookup-var s)]
             t))]
      t))

  (defn type-infer* [expr]
    (domonad
      [st (fetch-state)
       :let [_ (if (nil? st)
                 (throw (ex-info "nil state!" {:expr expr})))]
       r (condp #(%1 %2) expr
           integer? (m-result t/integer)
           string? (m-result t/string)
           boolean? (m-result t/boolean)
           float? (m-result t/float)
           vector? (domonad
                     [val-types (m-map type-infer* expr)
                      t (m-reduce <unify val-types)]
                     (t/vector-of t))
           local-var-symbol? (domonad
                               [vars (fetch-val ::state/vars)]
                               (or (get vars expr)
                                   (throw (ex-info "Local var not found"
                                                   {:var expr
                                                    ::state/vars vars}))))
           class-symbol? (type-infer* (resolve expr))
           qualified-symbol? (ti-qualified-symbol expr)
           sf-invoke? (ti-special-form expr)
           function-call? (ti-function-call expr)
           class? (m-result (t/class expr)))]
      r)))

(defn type-infer [expr]
  (first ((type-infer* expr) state/empty)))

(comment
  ((domonad state-m
            [x (fetch-val :foo)]
            x)
   {:foo 2})

  (type-infer (macroexpand `(let [x# 1] x#)))

  (type-infer [1 2 3])

  (type-infer
   (nth (source `inc) 2))

  (type-infer
   '((clojure.core/fn [x__46809__auto__] (clojure.core/inc x__46809__auto__))
     1.0))
  )
