(ns goedel.type-infer
  (:refer-clojure :exclude [core])
  (:require [better-cond.core :refer [cond]]
            [clojure.core.match :refer [match]]
            [clojure.repl :as repl]
            [goedel.protocols :as p]
            [goedel.type :as t]
            [goedel.type-infer.state :as state :refer [*state* with-state]]
            [goedel.type.refinement :as ref]
            [clojure.string :as str]))

(def special-form?
  #{`let*
    `do
    'clojure.core/def
    'def
    `fn
    `fn*
    `if
    '.
    'new
    `in-ns
    'quote
    'throw})

(defn- invocation? [expr]
  (or (instance? clojure.lang.Cons expr)
      (instance? clojure.lang.PersistentList expr)
      (instance? clojure.lang.LazySeq expr)))

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
       (or (some #{\.} (name s))
           (class? (resolve s)))))

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

     (and (t/type-var? t1)
          (t/type-var? t2))
     (do (state/set-var! t1 t2)
         (state/set-var! t2 t1)
         t2)

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

(defn get-method [cls method arg-ts]
  (let [m (name method)
        arg-clss (into-array Class (map p/as-java-class arg-ts))]
    (try
      (.getMethod cls m arg-clss)
      (catch NoSuchMethodException _e
        (or (->> cls
                 .getMethods
                 (filter
                  (fn [candidate-method]
                    (and (= (.getName candidate-method) m)
                         (every? true?
                                 (map #(.isAssignableFrom %1 %2)
                                      (.getParameterTypes candidate-method)
                                      arg-clss)))))
                 first)
            (throw (NoSuchMethodException.
                    (str (.getName cls) "." (name method)
                         "("
                         (str/join ", " (map #(.getName %) arg-clss))
                         ")"))))))))

(defn ti-method-invoke [obj m args]
  (let [obj-t (type-infer obj)
        arg-ts (doall (map type-infer args))]
    (println "inferring!" m)
    (println "arg types:" arg-ts)
    (letfn
        [(go
           [obj-t m arg-ts]
           (if-let [existentials
                    (->> arg-ts
                         (cons obj-t)
                         (mapcat
                          (fn [t]
                            (cond
                              (t/existential? t) [t]
                              (t/dependent? t) (do
                                                 (println "arg type depends on"
                                                          (::t/dependent-args t))
                                                (::t/dependent-args t)))))
                         seq)]
             (t/dependent
              existentials
              (fn [existential-type-map]
                (println "instantiating!" m)
                (let [obj-t* (if (t/existential? obj-t)
                               (state/resolve-var existential-type-map obj-t)
                               obj-t)
                      arg-ts* (doall (for [t arg-ts]
                                (cond
                                  (t/existential? t)
                                  (do
                                    (println "looking for existential" t "in"
                                             (keys existential-type-map))
                                    (println "x is" (get existential-type-map 'x)
                                             (state/resolve-var existential-type-map 'x))
                                    (doto (state/resolve-var existential-type-map t)
                                      (println "found")))
                                  (t/dependent? t)
                                  (instantiate-dependent t existential-type-map)
                                  :else t)) )
                      _ (println arg-ts*)]
                  ;; this'll be fun
                  ;; hope it halts!
                  (go obj-t* m arg-ts*))))
             (loop [obj-t obj-t]
               (cond
                 (class? obj-t)
                 (-> obj-t
                     (get-method m arg-ts)
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
  (let [[[vars & body]] (cond
                          ((some-fn list?
                                    #(instance? clojure.lang.Cons %))
                           (first args))
                          args
                          (symbol? (first args))
                          (rest args)
                          :else
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

(defmethod ti-special-form `. [[_ obj & args]]
  (let [[m args] (cond
                   (seq? (first args))
                   [(ffirst args) (-> args first rest)]
                   (symbol? (first args))
                   [(first args) (rest args)])]
    (ti-method-invoke obj m args)))

(defmethod ti-special-form 'new [[_ cls & args]]
  (let [cls-t (type-infer cls)
        arg-ts (doall (map type-infer args))]
    ;; TODO unify arg-ts with constructor-ts
    cls-t))

(defmethod ti-special-form `in-ns [[_ [_quote ns-name-sym]]]
  (state/assoc! ::state/ns (create-ns ns-name-sym))
  t/namespace)

(defmethod ti-special-form 'quote [[_ body]]
  (condp #(%1 %2) body
    symbol? (ref/exact t/symbol body)))

(defmethod ti-special-form 'throw [[_ ex-t]]
  ;; TODO
  t/bot
  )

;;;

(defn instantiate-dependent [{::t/keys [dependent-args dependent-fn]} vs]
  (dependent-fn
   (into {}
         (map (fn [[k v]] [(if (some #{k} dependent-args)
                             (t/universal->existential k)
                             k)
                           v]))
         vs)))

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

(defn ti-map [expr]
  ;; TODO
  (t/map-of t/top t/top))

(defn ti-local-var-symbol [expr]
  (or (state/lookup-var expr)
      (when (ns-resolve (the-ns 'clojure.core)
                        expr)
        (ti-qualified-symbol (symbol "clojure.core" (name expr))))
      (throw (ex-info "Local var not found" {:var expr}))))

(defn type-infer [expr]
  (println "inferring" expr)
  (let [expr (macroexpand expr)]
    (with-state
      (condp #(%1 %2) expr
        integer? (ref/exact t/integer expr)
        string? (ref/exact t/string expr)
        boolean? (ref/exact t/boolean expr)
        float? (ref/exact t/float expr)
        keyword? (ref/exact t/keyword expr)
        vector? (ti-vector expr)
        map? (ti-map expr)
        class-symbol? (type-infer (resolve expr))
        local-var-symbol? (ti-local-var-symbol expr)
        qualified-symbol? (ti-qualified-symbol expr)
        sf-invoke? (ti-special-form expr)
        function-call? (ti-function-call expr)
        class? (t/class expr)
        nil? t/bot))))
