(ns goedel.type.refinement
  (:refer-clojure :exclude [== and or])
  (:require [clojure.core.logic :as l :refer :all]
            [clojure.core :as c]))

(defn and [r₁ r₂]
  (fn [t]
    (when r₁ (r₁ t))
    (when r₂ (r₂ t))))

(defn or [r₁ r₂]
  (fn [t]
    (conde [(c/or r₁ succeed)]
           [(c/or r₂ succeed)])))

(defmacro refine [t r]
  `(-> ~t
       (update ::refinement and ~r)
       (update ::form #(if % (list `and % '~r) '~r))))

(defn intersect? [r₁ r₂]
  (or (= r₁ r₂)
      (c/and (some? r₁) (some? r₂)
             (seq (run 1 [τ] (r₁ τ) (r₂ τ))))))

(comment
  (intersect? #(l/== % 1) #(l/== % 1))
  (intersect? nil #(== % 1))

  (run 1 [t]
    (fail t))

  (run 2 [t]
    (conde
     [succeed]
     [(l/== t 2)]))
  )

;;;

(defn exact [t val]
  (refine t #(l/== % val)))

(defn member [t options]
  (refine t #(membero % options)))
