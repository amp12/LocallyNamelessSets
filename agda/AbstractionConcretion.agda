module AbstractionConcretion where

open import Prelude
open import Unfinite
open import oc-Sets
open import Freshness
open import LocalClosedness
open import Support

----------------------------------------------------------------------
-- Locally closed part of an oc-set [Definition 2.14]
----------------------------------------------------------------------
lc : (i : ℕ)(X : Set){{_ : oc X}} → Set
lc i X = ∑ x ∶ X , i ≻ x

----------------------------------------------------------------------
-- Abstraction & Concretion [Equation (13)]
----------------------------------------------------------------------
module _ {X : Set}{{_ : lns X}} where
  abs : 𝔸 → X → X     -- paper's notation: \ᵃx
  abs a x = (0 <~ a)x

  conc : X → 𝔸 → X    -- paper's notation: xᵃ
  conc x a = (0 ~> a)x

  conc-lc : ∀ x a → 1 ≻ x → 0 ≻ conc x a -- Equation (14)
  conc-lc _ _ = ~>index-supports'

  abs-lc : ∀ a x → 0 ≻ x → 1 ≻ abs a x -- Equation (15)
  abs-lc _ _ = <~index-supports

  abs-conc : ∀ a x → (_ : a # x) → abs a (conc x a) ≡ x -- Equation (16)
  abs-conc _ _ = close-open-var

  conc-abs : ∀ a x → (_ : 0 ≻ x) → conc (abs a x) a ≡ x -- Equation (17)
  conc-abs _ _ = open-close-var

----------------------------------------------------------------------
-- "Body" predicate [Remark 2.15]
----------------------------------------------------------------------
module Body {X : Set}{{_ : lns X}} where
  body : X → Set
  body x = И a ∶ 𝔸 , 0 ≻ conc x a

  body→1≻ : ∀ x → body x → 1 ≻ x -- Equation (18)
  body→1≻ x p with (a , ∉∪) ← fresh{𝔸} (Иe₁ (asupp x) ∪ Иe₁ p) =
    subst (1 ≻_) (abs-conc a x (Иe₂ (asupp x) a))
    (abs-lc a (conc x a) (Иe₂ p a))

  1≻→body : ∀ x → 1 ≻ x → body x -- Equation (18), cont.
  1≻→body x p = Иi Ø λ a → conc-lc x a p
