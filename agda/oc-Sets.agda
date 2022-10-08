module oc-Sets where

open import Prelude
open import Unfinite

----------------------------------------------------------------------
-- oc-Sets [Section 2.2]
----------------------------------------------------------------------
record oc (X : Set) : Set where
  constructor mkoc
  infix 5 _~>_ _<~_
  field
    _~>_ : ℕ → 𝔸 → X → X
    _<~_ : ℕ → 𝔸 → X → X
    -- [Figure 1]
    oc₁ :
      (i : ℕ)
      (a b : 𝔸)
      (x : X)
      → -----------------------------
      (i ~> a)((i ~> b)x) ≡ (i ~> b)x
    oc₂ :
      (i j : ℕ)
      (a : 𝔸)
      (x : X)
      → -----------------------------
      (i <~ a)((j <~ a)x) ≡ (j <~ a)x
    oc₃ :
      (i : ℕ)
      (a : 𝔸)
      (x : X)
      → -----------------------------
      (i <~ a)((i ~> a)x) ≡ (i <~ a)x
    oc₄ :
      (i : ℕ)
      (a : 𝔸)
      (x : X)
      → -----------------------------
      (i ~> a)((i <~ a)x) ≡ (i ~> a)x
    oc₅ :
      (i j : ℕ)
      (a b : 𝔸)
      (x : X)
      {{_ : i ≠ j}}
      → ---------------------------------------
      (i ~> a)((j ~> b)x) ≡ (j ~> b)((i ~> a)x)
    oc₆ :
      (i j : ℕ)
      (a b : 𝔸)
      (x : X)
      {{_ : a ≠ b}}
      → ---------------------------------------
      (i <~ a)((j <~ b)x) ≡ (j <~ b)((i <~ a)x)
    oc₇ :
      (i j : ℕ)
      (a b : 𝔸)
      (x : X)
      {{_ : i ≠ j}}
      {{_ : a ≠ b}}
      → ---------------------------------------
      (i ~> a)((j <~ b)x) ≡ (j <~ b)((i ~> a)x)
    oc₈ :
      (i j : ℕ)
      (a b : 𝔸)
      (x : X)
      → -----------------------------------------------------------
      (i ~> b)((i <~ a)((j ~> b)x)) ≡ (j ~> b)((j <~ a)((i ~> a)x))
    oc₉ :
      (i j : ℕ)
      (a b : 𝔸)
      (x : X)
      → -----------------------------------------------------------
      (j <~ a)((i ~> a)((j <~ b)x)) ≡ (j <~ b)((i ~> b)((i <~ a)x))

open oc{{...}} public

{-# DISPLAY oc._~>_ _ i a = i ~> a #-}
{-# DISPLAY oc._<~_ _ i a = i <~ a #-}

----------------------------------------------------------------------
-- Example: oc-set of indices and atoms [Example 2.2]
----------------------------------------------------------------------
ℕ𝔸 : Set
ℕ𝔸 = ℕ ⊎ 𝔸

private
  opn : ℕ → 𝔸 → ℕ𝔸 → ℕ𝔸
  opn i a (ι₁ j) = if does(i ≐ j) then ι₂ a else ι₁ j
  opn i a (ι₂ b) = ι₂ b

  cls : ℕ → 𝔸 → ℕ𝔸 → ℕ𝔸
  cls i a (ι₁ j) = ι₁ j
  cls i a (ι₂ b) = if does(a ≐ b) then ι₁ i else ι₂ b

  ax₁ :
    (i : ℕ)
    (a b : 𝔸)
    (x : ℕ𝔸)
    → -----------------------------
    opn i a (opn i b x) ≡ opn i b x
  ax₁ i _ _ (ι₁ j) with i ≐ j
  ... | neq f rewrite dec-neq i j f = refl
  ... | equ = refl
  ax₁ i _ _ (ι₂ _) = refl

  ax₂ :
    (i j : ℕ)
    (a : 𝔸)
    (x : ℕ𝔸)
    → -----------------------------
    cls i a (cls j a x) ≡ cls j a x
  ax₂ _ _ _ (ι₁ _) = refl
  ax₂ _ _ a (ι₂ b) with  a ≐ b
  ... | neq f rewrite dec-neq a b f = refl
  ... | equ = refl

  ax₃ :
    (i : ℕ)
    (a : 𝔸)
    (x : ℕ𝔸)
    → -----------------------------
    cls i a (opn i a x) ≡ cls i a x
  ax₃ i a (ι₁ j) with i ≐ j
  ... | neq _ = refl
  ... | equ rewrite dec-equ a = refl
  ax₃ _ _ (ι₂ _) = refl

  ax₄ :
    (i : ℕ)
    (a : 𝔸)
    (x : ℕ𝔸)
    → -----------------------------
    opn i a (cls i a x) ≡ opn i a x
  ax₄ i a (ι₁ j) = refl
  ax₄ i a (ι₂ b) with a ≐ b
  ... | neq _ = refl
  ... | equ rewrite dec-equ i = refl

  ax₅ :
    (i j : ℕ)
    (a b : 𝔸)
    (x : ℕ𝔸)
    {{p : i ≠ j}}
    → ---------------------------------------
    opn i a (opn j b x) ≡ opn j b (opn i a x)
  ax₅ _ j _ _ (ι₁ k)       with j ≐ k
  ax₅ i _ _ _ (ι₁ k)       | neq _ with  i ≐ k
  ax₅ _ j _ _ (ι₁ k)       | neq f | neq _ rewrite dec-neq j k f = refl
  ax₅ _ _ _ _ (ι₁ _)       | neq _ | equ                         = refl
  ax₅ _ j _ _ (ι₁ _) {{p}} | equ rewrite p | dec-equ j           = refl
  ax₅ _ _ _ _ (ι₂ _)                                             = refl

  ax₆ :
    (i j : ℕ)
    (a b : 𝔸)
    (x : ℕ𝔸)
    {{p : a ≠ b}}
    → ---------------------------------------
    cls i a (cls j b x) ≡ cls j b (cls i a x)
  ax₆ _ _ _ _ (ι₁ _)                                             = refl
  ax₆ _ _ _ b (ι₂ c)       with  b ≐ c
  ax₆ _ _ a _ (ι₂ c)       | neq _ with a ≐ c
  ax₆ _ _ _ b (ι₂ c)       | neq f | neq _ rewrite dec-neq b c f = refl
  ax₆ _ _ _ _ (ι₂ _)       | neq _ | equ                         = refl
  ax₆ _ _ _ b (ι₂ _) {{p}} | equ rewrite p | dec-equ b           = refl

  ax₇ :
    (i j : ℕ)
    (a b : 𝔸)
    (x : ℕ𝔸)
    {{p : i ≠ j}}
    {{q : a ≠ b}}
    → ---------------------------------------
    opn i a (cls j b x) ≡ cls j b (opn i a x)
  ax₇ i _ _ _ (ι₁ k)           with i ≐ k
  ax₇ _ _ _ _ (ι₁ _)           | neq _                   = refl
  ax₇ _ _ a b (ι₁ _) {{q = q}} | equ rewrite symm≠ a b q = refl
  ax₇ _ _ _ b (ι₂ c)           with b ≐ c
  ax₇ _ _ _ _ (ι₂ _)           | neq _                   = refl
  ax₇ _ _ _ _ (ι₂ _) {{p}}     | equ rewrite p           = refl

  ax₈ :
    (i j : ℕ)
    (a b : 𝔸)
    (x : ℕ𝔸)
    → -----------------------------------------------------------
    opn i b (cls i a (opn j b x)) ≡ opn j b (cls j a (opn i a x))
  ax₈ _ j _ _ (ι₁ k) with j ≐ k
  ax₈ i _ _ _ (ι₁ k) | neq _ with i ≐ k
  ax₈ _ j _ _ (ι₁ k) | neq f | neq _
      rewrite dec-neq j k f         = refl
  ax₈ _ j a _ (ι₁ _) | neq _ | equ
      rewrite dec-equ a | dec-equ j = refl
  ax₈ _ _ a b (ι₁ _) | equ   with a ≐ b
  ax₈ i j _ _ (ι₁ _) | equ   | neq _ with i ≐ j
  ax₈ _ j _ _ (ι₁ -) | equ   | neq _ | neq _
      rewrite dec-equ j = refl
  ax₈ _ j a _ (ι₁ _) | equ   | neq _ | equ
      rewrite dec-equ a | dec-equ j = refl
  ax₈ i j _ _ (ι₁ _) | equ   | equ   with i ≐ j
  ax₈ i j _ _ (ι₁ _) | equ   | equ   | neq _
      rewrite dec-equ i | dec-equ j = refl
  ax₈ _ j a _ (ι₁ _) | equ   | equ   | equ
      rewrite dec-equ a | dec-equ j = refl
  ax₈ _ _ a _ (ι₂ c) with a ≐ c
  ax₈ _ _ _ _ (ι₂ _) | neq _      = refl
  ax₈ i j _ _ (ι₂ _) | equ
      rewrite dec-equ i | dec-equ j = refl

  ax₉ :
    (i j : ℕ)
    (a b : 𝔸)
    (x : ℕ𝔸)
    → -----------------------------------------------------------
    cls j a (opn i a (cls j b x)) ≡ cls j b (opn i b (cls i a x))
  ax₉ i _ _ _ (ι₁ k) with i ≐ k
  ax₉ _ _ _ _ (ι₁ _) | neq _ = refl
  ax₉ _ _ a b (ι₁ _) | equ
      rewrite dec-equ a | dec-equ b = refl
  ax₉ _ _ _ b (ι₂ c) with  b ≐ c
  ax₉ _ _ a _ (ι₂ c) | neq _ with a ≐ c
  ax₉ _ _ _ b (ι₂ c) | neq f | neq _
      rewrite dec-neq b c f = refl
  ax₉ i _ _ b (ι₂ _) | neq _ | equ
      rewrite dec-equ i | dec-equ b = refl
  ax₉ i j _ _ (ι₂ _) | equ   with i ≐ j
  ax₉ _ _ a b (ι₂ _) | equ   | neq _ with a ≐ b
  ax₉ _ _ _ b (ι₂ _) | equ   | neq _ | neq _
      rewrite dec-equ b = refl
  ax₉ i _ _ b (ι₂ _) | equ   | neq _ | equ
      rewrite dec-equ i | dec-equ b = refl
  ax₉ _ _ a b (ι₂ _) | equ   | equ   with a ≐ b
  ax₉ _ _ a b (ι₂ _) | equ   | equ   | neq _
      rewrite dec-equ a | dec-equ b = refl
  ax₉ i _ _ b (ι₂ _) | equ   | equ   | equ
      rewrite dec-equ i | dec-equ b = refl

instance
  ocℕ𝔸 : oc ℕ𝔸
  ocℕ𝔸 = mkoc opn cls ax₁ ax₂ ax₃ ax₄ ax₅ ax₆ ax₇ ax₈ ax₉

----------------------------------------------------------------------
-- ℕ𝔸 is unfinite
----------------------------------------------------------------------
instance
  Unfiniteℕ𝔸 : Unfinite ℕ𝔸
  Unfiniteℕ𝔸 = Unfinite⊎
