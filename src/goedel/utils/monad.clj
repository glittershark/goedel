(ns goedel.utils.monad
  (:require [clojure.algo.monads :as monads :refer [defmonadfn domonad m-seq m-fmap]]
            [clojure.core.match :refer [match]]))


(defn update-val
  [k f & args]
  (monads/update-val k #(apply f % args)))

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
      :let [ilist (apply list iforms)]
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

(defmonadfn m-update
  ([m k f] (m-fmap (partial assoc m k) (f (get m k))))
  ([m k f x] (m-fmap (partial assoc m k) (f (get m k) x)))
  ([m k f x y] (m-fmap (partial assoc m k) (f (get m k) x y)))
  ([m k f x y z] (m-fmap (partial assoc m k) (f (get m k) x y z)))
  ([m k f x y z & more] (m-fmap (partial assoc m k)
                                (apply f (get m k) x y z more))))
