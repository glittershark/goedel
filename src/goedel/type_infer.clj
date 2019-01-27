(ns goedel.type-infer
  (:refer-clojure :exclude [core])
  (:require [better-cond.core :refer [cond]]
            [clojure.repl :as repl]
            [goedel.protocols :as p]
            [goedel.type :as t]
            [goedel.type-infer.state :as state :refer [*state* with-state]]
            [goedel.type.refinement :as ref]))

(def special-form?
  #{`let*
    `do
    'clojure.core/def
    'def
    `fn
    `fn*
    `if
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

(defn source [f]
  (-> f
      repl/source-fn
      read-string
      macroexpand))

;;;

(defn ∧unify
  "unify covariantly up the lattice"
  ([] t/top)
  ([t1] t1)
  ([t1 t2]
   (cond
     (= t1 t/top) t/top
     (= t1 t2) t2

     (t/type-var? t1) (let [t2′ (ref/unrefine t2)]
                        (state/set-var! t1 t2)
                        t2)

     (t/type-var? t2) (∧unify t2 t1)

     :let [ref1 (::ref/refinement t1)
           ref2 (::ref/refinement t2)]
     (and (= (::t/type t1) (::t/type t2))
          (= (count (::t/type-args t1))
             (count (::t/type-args t2))))
     (if (or (not ref1)
             (not ref2)
             (ref/intersect? (::ref/refinement ref1)
                             (::ref/refinement ref2)))
       (let [args (doall
                   (map ∧unify (::t/type-args t1) (::t/type-args t2)))]
         (-> t1
             (assoc ::t/type-args args)
             (ref/∧unify-refinements t2)))
       t/bot)

     :else (t/sup t1 t2))))

(defn ∨unify
  "unify contravariantly down the lattice"
  ([] t/top)
  ([t1] t1)
  ([t1 t2]
   (cond
     (= t1 t/top) t2
     (= t1 t2) t2
     :else (throw (ex-info "Could not unify"
                           {:types [t1 t2]})))))


;;;

(declare type-infer)

(defn ti-method-invoke [obj m args]
  (let [obj-t (type-infer obj)
        arg-ts (doall (map type-infer args))]
    (letfn
        [(go
           [obj-t m arg-ts]
           (if-let [existentials (->> arg-ts
                                      (cons obj-t)
                                      (filter t/existential?)
                                      seq)]
             (t/dependent
              existentials
              (fn [existential-type-map]
                (let [obj-t* (if (t/existential? obj-t)
                               (get existential-type-map obj)
                               obj-t)
                      arg-ts* (replace existential-type-map arg-ts)]
                  ;; this'll be fun
                  ;; hope it halts!
                  (go obj-t* m arg-ts*))))
             (loop [obj-t obj-t]
               (cond
                 (class? obj-t)
                 (-> obj-t
                     (.getMethod
                      (name m)
                      (into-array Class (map p/as-java-class arg-ts)))
                     .getReturnType
                     t/class->type)
                 (class-symbol? obj-t)
                 (recur (resolve obj-t))
                 (= ::t/class (::t/type obj-t))
                 (recur (-> obj-t ::t/type-args first))
                 (nil? obj-t)
                 (throw (NullPointerException.))
                 :else
                 (recur (class obj-t))))))]
      (go obj-t m arg-ts))))

(defmulti ti-special-form first)

(defmethod ti-special-form `do [[_ & body]]
  (last (map type-infer body)))

(defmethod ti-special-form `let* [[_ vars & body]]
  (let [vs (doall
            (map (fn [[v x]]
                   (let [t (type-infer x)]
                     (state/set-var! v t)
                     v))
                 (partition 2 vars)) )
        res (type-infer `(do ~@body))]
    (dorun (map #(state/update! ::state/vars dissoc %) vs))
    res))

(defmethod ti-special-form `def [[_ n v]]
  (let [t (type-infer v)
        vname (symbol (some-> @*state* ::state/ns ns-name name) (name n))]
    (state/set-var! vname t)
    t/var))

(defmethod ti-special-form `fn [[_ & args]]
  ;; TODO handle multiple arities
  (let [[[vars & body]] (if ((some-fn list?
                                      #(instance? clojure.lang.Cons %))
                             (first args))
                          args
                          [args])]
    (let [arg-vars (doall
                    (map (fn [v]
                           (let [tv (state/new-exist-var!)]
                             (state/set-var! v tv)
                             tv))
                         vars) )
          res (type-infer `(do ~@body))
          arg-tys (doall (map #(or (state/lookup-var %) %) arg-vars))]
      (dorun (map #(state/update! ::state/vars dissoc %) arg-vars))
      (t/universalize
       (t/-> (t/types* arg-tys) res)))))
(defmethod ti-special-form `fn* [[_ & args]]
  (ti-special-form (cons `fn args)))

(defmethod ti-special-form `if [[_ _cond then else]]
  (let [then-t (type-infer then)
        else-t (type-infer else)]
    (∧unify then-t else-t)))

(defmethod ti-special-form `. [[_ obj [m & args]]]
  (ti-method-invoke obj m args))

;;;

(defn instantiate-dependent [{::t/keys [dependent-args dependent-fn]} vs]
  (dependent-fn
   (into {}
         (map (fn [[k v]] [(t/universal->existential k) v]))
         (select-keys vs dependent-args))))

(defn subs-universals [t]
  (t/prewalk
   (fn [x]
     (let [vs (::state/vars @*state*)]
       (cond
         (and (t/universal? x) (contains? vs x)) (get vs x)
         (t/dependent? x) (instantiate-dependent x vs)
         :else x)))
   t))

(defn ti-function-call [[f & args]]
  (let [arg-tys (doall (map type-infer args))
        ft (type-infer f)
        rv (state/new-exist-var!)]
    (-> ft
        (∧unify (t/-> (t/types* arg-tys) rv))
        subs-universals
        t/return-type)))

(defn lookup-and-type-infer [s]
  (let [src (source s)
        old-ns (::state/ns @*state*)
        _ (state/assoc! ::state/ns (-> s namespace symbol the-ns))
        r (type-infer src)
        _ (state/assoc! ::state/ns old-ns)]
    r))

(defn ti-qualified-symbol [s]
  (or (state/lookup-var s)
      (do
        (lookup-and-type-infer s)
        (state/lookup-var s))))

(defn ti-vector [vec-expr]
  (let [val-types (doall (map type-infer vec-expr))
        t (reduce ∧unify val-types)]
    (t/vector-of t)))

(defn type-infer [expr]
  (with-state
    (condp #(%1 %2) expr
      integer? (ref/exact t/integer expr)
      string? (ref/exact t/string expr)
      boolean? (ref/exact t/boolean expr)
      float? (ref/exact t/float expr)
      keyword? (ref/exact t/keyword expr)
      vector? (ti-vector expr)
      local-var-symbol? (or (state/lookup-var expr)
                            (throw (ex-info "Local var not found" {:var expr})))
      class-symbol? (type-infer (resolve expr))
      qualified-symbol? (ti-qualified-symbol expr)
      sf-invoke? (ti-special-form expr)
      function-call? (ti-function-call expr)
      class? (t/class expr))))
