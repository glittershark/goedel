(ns goedel.type-infer.state
  (:refer-clojure :exclude [empty assoc!])
  (:require [goedel.type :as t]))

(def empty
  {::exist-type-vars {}
   ::vars {}
   ::counter 0
   ::ns nil})

(def ^:dynamic *state* nil)


(defmacro with-state
  {:indent/style 0}
  [& body]
  `(binding [*state* (or *state* (atom empty))]
     ~@body))

(defn lookup-var [vname]
  (get-in @*state* [::vars vname]))

(defn assoc! [& kvs]
  (apply swap! *state* assoc kvs))

(defn update! [k f & args]
  (apply swap! *state* update k f args))

(defn set-var! [v t]
  (update! ::vars assoc v t))

(defn new-exist-var! []
  (-> (swap! *state*
             (fn [{::keys [counter] :as s}]
               (-> s
                   (update ::counter inc)
                   (update ::exist-type-vars
                           assoc (t/existential counter) nil))))
      ::counter
      dec
      (t/existential )))

(defn resolve-var
  ([v] (resolve-var (::vars @*state*) v))
  ([vs v]
   (loop [curr v
          seen #{v}]
     (if-let [next (get vs curr)]
       (cond
         (seen next) (throw (ex-info "Loop in type vars" {:seen seen}))
         (t/type-var? next) (recur next (conj seen next))
         :else next)
       curr))))
