(ns goedel.type.refinement
  (:refer-clojure :exclude [== and or])
  (:require [clojure.core :as c]
            [clojure.core.logic :as l :refer :all]
            [clojure.walk :as walk]
            [goedel.type.refinement :as ref]))

(defn and [r₁ r₂]
  (fn [t]
    (when r₁ (r₁ t))
    (when r₂ (r₂ t))))

(defn or [r₁ r₂]
  (fn [t]
    (conde [(c/or (r₁ t) succeed)]
           [(c/or (r₂ t) succeed)])))

(defmacro refine [t r]
  (let [new-form (walk/postwalk
                  (fn [x]
                    (cond
                      (list? x) (list `list x)
                      (and (symbol? x)
                           (contains? &env x)) x
                      (symbol? x) (list `quote x)
                      :else x))
                  r)]
    `(-> ~t
         (update ::refinement and ~r)
         (update ::form #(if % (list `and % '~new-form) '~new-form)))))

(defmacro refine-disjoint [t r]
  (let [new-form (walk/postwalk
                  (fn [x]
                    (cond
                      (list? x) (list `list x)
                      (and (symbol? x)
                           (contains? &env x)) x
                      (symbol? x) (list `quote x)
                      :else x))
                  r)]
    `(-> ~t
         (update ::refinement and ~r)
         (update ::form #(if % (list `or % '~new-form) '~new-form)))))

(defn ∧unify-refinements [t1 t2]
  (if-let [ref2 (::refinement t2)]
    (-> t1
        (update ::refinement or ref2)
        (update ::form #(if % (list `or % (::form t2)) (::form t2))))
    t1))

;;;

(defn intersect? [r₁ r₂]
  (c/or (= r₁ r₂)
      (c/and (some? r₁) (some? r₂)
             (seq (run 1 [τ] (r₁ τ) (r₂ τ))))))

(defn exact [t val]
  (-> t
      (update ::refinement and #(l/== % val))
      (update ::form (fn [t] (if t
                               (list `and t `#(l/== % ~val))
                               `#(l/== % ~val))))))

(defmacro member [t options]
  `(refine ~t #(membero % ~options)))

(defn unrefine [t]
  (dissoc t ::refinement ::form))
