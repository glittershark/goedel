(ns goedel.type.lattice-test
  (:require [clojure.test :refer :all]
            [goedel.type.lattice :as sut]
            [ubergraph.core :as uber]))

(def diamond
  (uber/digraph
   [::⊥ ::n₁]
   [::⊥ ::n₂]
   [::n₁ ::⊤]
   [::n₂ ::⊤]))

(def quad-diamond
  (uber/digraph
   [::⊥ ::α₁]
   [::⊥ ::α₂]
   [::α₁ ::β₁]
   [::α₁ ::β₂]
   [::α₂ ::β₂]
   [::α₂ ::β₃]
   [::β₁ ::γ₁]
   [::β₂ ::γ₁]
   [::β₂ ::γ₂]
   [::β₃ ::γ₂]
   [::γ₁ ::⊤]
   [::γ₂ ::⊤]))

(def star-trek
  (uber/digraph
   [::α₁ ::β]
   [::α₂ ::β]
   [::β ::⊤]
   [::α₁ ::⊤]
   [::α₂ ::⊤]
   [::⊥ ::α₁]
   [::⊥ ::α₂]))

(comment
  (uber/viz-graph diamond)
  (uber/viz-graph quad-diamond)
  (uber/viz-graph star-trek)
  )

(deftest lattice?-test
  (is (sut/lattice? diamond))
  (is (sut/lattice? quad-diamond)))

(deftest sub-test
  (is (= ::⊥ (sut/∨ diamond ::n₁ ::n₂))))

(deftest sup-test
  (is (= ::⊤ (sut/∧ diamond ::n₁ ::n₂)))
  (is (= ::β (sut/∧ star-trek ::α₁ ::α₂))
      "finds the *least* common parent"))
