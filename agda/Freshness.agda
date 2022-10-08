module Freshness where

open import Prelude
open import Unfinite
open import oc-Sets

----------------------------------------------------------------------
-- Freshness [Section 2.3]
----------------------------------------------------------------------
infix 4 _#_
_#_ : {X : Set}{{_ : oc X}} → 𝔸 → X → Set
a # x = (0 <~ a)x ≡ x -- Equation (3)

module _ {X : Set}{{_ : oc X}} where
  #1 : -- Equation (4)
    {i j : ℕ}
    {a : 𝔸}
    {x : X}
    (p : (i <~ a)x ≡ x)
    → -----------------
    (j <~ a)x ≡ x
  #1 {i = i} {j} {a} {x} p =
    proof
      (j <~ a)x
    ≡[ (ap (j <~ a) (symm p)) ]
      (j <~ a)((i <~ a)x)
    ≡[ oc₂ _ _ _ _ ]
    (i <~ a)x
    ≡[ p ]
      x
    qed

  #2 : -- Lemma 2.4
    {a : 𝔸}
    {x : X}
    {i : ℕ}
    (p : a # x)
    → -----------
    (i <~ a)x ≡ x
  #2 = #1

  #3 : -- Lemma 2.4, cont.
    {a : 𝔸}
    {x : X}
    {i : ℕ}
    (p : (i <~ a)x ≡ x)
    → -----------------
    a # x
  #3 = #1

  close-open-var : -- Corollary 2.5
    {a : 𝔸}
    {x : X}
    {i : ℕ}
    (p : a # x)
    → ---------------------
    (i <~ a)((i ~> a)x) ≡ x
  close-open-var {a} {x} {i} p =
    proof
      (i <~ a)((i ~> a)x)
    ≡[ oc₃ _ _ _ ]
      (i <~ a)x
    ≡[ #1 p ]
      x
    qed
