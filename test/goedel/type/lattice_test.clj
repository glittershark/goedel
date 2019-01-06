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
   [::β₂ ::γ₂]
   [::β₂ ::γ₂]
   [::β₃ ::γ₂]
   [::γ₁ ::⊤]
   [::γ₂ ::⊤]))

(deftest lattice?-test
  (is (sut/lattice? diamond))
  (is (sut/lattice? quad-diamond)))

(deftest sub-test
  (is (= ::⊥ (sut/∨ diamond ::n₁ ::n₂))))

(deftest sup-test
  (is (= ::⊤ (sut/∧ diamond ::n₁ ::n₂))))
