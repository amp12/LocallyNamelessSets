module fsRenset where

open import Prelude
open import Unfinite
open import oc-Sets
open import Freshness
open import LocalClosedness
open import Support
open import AbstractionConcretion
open import RenamingRendexingSwapping
open import Category

-- Given an unfinite set S
module _ {S : Set}{{_  : Unfinite S}} where
  --------------------------------------------------------------------
  -- Popescu's finitely supported rensets
  --------------------------------------------------------------------
  record Renset (X : Set) : Set where
    field
      ρ : S → S → X → X
      RN₁ :
        (a : S)
        (x : X)
        → ---------
        ρ a a x ≡ x
      RN₂ :
        (a b c : S)
        (x : X)
        {{_ : a ≠ c}}
        → -----------------------
        ρ b a (ρ c a x) ≡ ρ c a x
      RN₃ :
        (a b c : S)
        (x : X)
        → -------------------------------
        ρ c b (ρ b a x) ≡ ρ c a (ρ c b x)
      RN₄ :
        (a b c d : S)
        (x : X)
        {{_ : b ≠ c}}
        {{_ : a ≠ c}}
        {{_ : d ≠ a}}
        → -------------------------------
        ρ b a (ρ d c x) ≡ ρ d c (ρ b a x)

  open Renset{{...}} public

  --------------------------------------------------------------------
  -- Renset freshness relation
  --------------------------------------------------------------------
  infix 4 _♯_
  _♯_ : {X : Set}{{_ : Renset X}} → S → X → Set
  a ♯ x = И b ∶ S , ρ b a x ≡ x

  ♯≡ :
    {X : Set}
    {{_ : Renset X}}
    (x : X)
    (a b : S)
    {{_ : a ♯ x}}
    → -----------
    ρ b a x ≡ x
  ♯≡ x a b {{Иi и₁ и₂}} =
    let
      as = [ a ] ∪ и₁
      c = new as
      e : ρ c a x ≡ x
      e = и₂ c {{∉∪₂ (unfinite as)}}
      instance
        _ : a ≠ c
        _ = symm≠ c a (∉[]₁ (∉∪₁ (unfinite as)))
    in
    proof
      ρ b a x
    ≡[ ap (ρ b a) (symm e) ]
      ρ b a (ρ c a x)
    ≡[ RN₂ _ _ _ _ ]
      ρ c a x
    ≡[ e ]
      x
    qed

  ♯ρ :
    {X : Set}
    {{_ : Renset X}}
    (x : X)
    (a b c : S)
    {{_ : c ♯ x}}
    {{_ : c ≠ b}}
    → -----------
    c ♯ ρ b a x
  ♯ρ x a b c with b ≐ a
  ... | equ rewrite RN₁ a x = it
  ... | neq f = Иi [ a ] и₂
    where
    и₂ :
      (d : S)
      {{_ : d ∉ [ a ]}}
      → -----------------------
      ρ d c (ρ b a x) ≡ ρ b a x
    и₂ d {{∉[]}} with c ≐ a
    ... | equ = RN₂ _ _ _ _
    ... | neq g =
      let
        instance
          _ : c ≠ a
          _ = ¬≡→≠ g
          _ : b ≠ c
          _ = symm≠ c b it
      in
      proof
        ρ d c (ρ b a x)
      ≡[ RN₄ _ _ _ _ _ ]
        ρ b a (ρ d c x)
      ≡[ ap (ρ b a) (♯≡ x c d) ]
        ρ b a x
      qed

  ♯ρ' :
    {X : Set}
    {{_ : Renset X}}
    (x : X)
    (a b : S)
    {{_ : a ≠ b}}
    → -----------
    a ♯ ρ b a x
  ♯ρ' x a b = Иi Ø λ _ → RN₂ _ _ _ _

  --------------------------------------------------------------------
  -- Finitely supported rensets
  --------------------------------------------------------------------
  record fsRenset (X : Set) : Set where
    field
      {{renset}} : Renset X
      rsupp : (x : X) → И a ∶ S , a ♯ x

  open fsRenset{{...}}public

---------------------------------------------------------------------
-- Index-index swapping [Equation (59)]
----------------------------------------------------------------------
infix 5 _≀ᵢᵢ_
_≀ᵢᵢ_ : {X : Set}{{_ : lns X}} → ℕ → ℕ → X → X
(i ≀ᵢᵢ j)x =
  let k = max (π₁ (isupp x)) ((max i j) +1) in
  (k ↦ j)((j ↦ i)((i ↦ k)x))

----------------------------------------------------------------------
-- Name-index swapping [Equations (60) & (61)]
----------------------------------------------------------------------
infix 5 _≀ᵢₐ_
_≀ᵢₐ_ : {X : Set}{{_ : lns X}} → ℕ → 𝔸 → X → X
(i ≀ᵢₐ a)x =
  let b = new ([ a ] ∪ Иe₁ (asupp x)) in
  (a ↤ b)((i <~ a)((i ~> b)x))

infix 5 _≀ₐᵢ_
_≀ₐᵢ_ : {X : Set}{{_ : lns X}} → 𝔸 → ℕ → X → X
(a ≀ₐᵢ i)x =
  let j = max (i +1) (π₁ (isupp x)) in
  (j ↦ i)((i ~> a)((j <~ a)x))

----------------------------------------------------------------------
-- Every locally nameless set is a finitely supported ℕ𝔸-renset
----------------------------------------------------------------------
{- Proposition 2.17 proves that every locally nameless set is a
finitely supported 𝔸-renset. As part of the proof of Proposition 3.8 we
prove that this extends to renaming with respect to the whole of ℕ𝔸 -}

-- First we show that every locally nameless set is a  ℕ𝔸-renset
lns→Renset :
  {X : Set}
  {{_ : lns X}}
  → -----------
  Renset{ℕ𝔸} X
lns→Renset {X} = record
  { ρ   = ren
  ; RN₁ = ren₁
  ; RN₂ = ren₂
  ; RN₃ = ren₃
  ; RN₄ = ren₄
  }
  where
  ren : ℕ𝔸 → ℕ𝔸 → X → X
  ren (ι₁ i) (ι₁ j) x = (j ↦ i)x
  ren (ι₁ i) (ι₂ a) x = (i <~ a)x
  ren (ι₂ a) (ι₁ i) x = (i ~> a)x
  ren (ι₂ a) (ι₂ b) x = (a ↤ b)x

  ren₁ :
    (a : ℕ𝔸)
    (x : X)
    → -----------
    ren a a x ≡ x
  ren₁ (ι₁ i) x =
    let
      as = Иe₁ (asupp x)
      a  = new as
      a#x : a # x
      a#x = Иe₂ (asupp x) a {{unfinite as}}
    in
    proof
      (i ↦ i)x
    ≡[]
      (i <~ a)((i ~> a)x)
    ≡[ oc₃ _ _ _ ]
      (i <~ a)x
    ≡[ #2 a#x ]
      x
    qed
  ren₁ (ι₂ _) _ = rn₁

  ren₂ :
    (a b c : ℕ𝔸)
    (x : X)
    {{_ : a ≠ c}}
    → -----------------------------
    ren b a (ren c a x) ≡ ren c a x
  ren₂ (ι₁ i) (ι₁ j) (ι₁ k) x =
    let
      as = Иe₁ (asupp x)
      a  = new as
      bs = [ a ] ∪ as
      b  = new bs
      instance
        _ : a # x
        _ = Иe₂ (asupp x) a {{unfinite as}}
        _ : b # x
        _ = Иe₂ (asupp x) b {{∉∪₂ (unfinite bs)}}
        _ : b ≠ a
        _ =  ∉[]₁ (∉∪₁ (unfinite bs))
        _ : b # (i ↦ k)x
        _ = #<~ k b a _ {{#~> i b a x}}
        _ : i ≠ k
        _ = ap≠ {A = ℕ} {ℕ𝔸} {ι₁} {i} {k} it
    in -- ri₂ i j k x
    proof
      (i ↦ j)((i ↦ k)x)
    ≡[ ↦fresh ((i ↦ k)x) b ]
      (j <~ b)((i ~> b)((i ↦ k)x))
    ≡[]
      (j <~ b)((i ~> b)((k <~ a)((i ~> a)x)))
    ≡[ ap (j <~ b) (oc₇ _ _ _ _ _) ]
      (j <~ b)((k <~ a)((i ~> b)((i ~> a)x)))
    ≡[ ap ((j <~ b) ∘ (k <~ a)) (oc₁ _ _ _ _) ]
      (j <~ b)((k <~ a)((i ~> a)x))
    ≡[ #2 it ]
      (k <~ a)((i ~> a)x)
    ≡[]
      (i ↦ k)x
    qed

  ren₂ (ι₁ i) (ι₁ j) (ι₂ c) x =
    let
      as = Иe₁ (asupp ((i ~> c)x))
      a  = new as
      instance
        _ : a # (i ~> c)x
        _ = Иe₂ (asupp ((i ~> c)x)) a {{unfinite as}}
    in
    proof
      (i ↦ j)((i ~> c) x)
    ≡[]
      (j <~ a)(((i ~> a)(((i ~> c) x))))
    ≡[ ap (j <~ a) (oc₁ _ _ _ _) ]
      (j <~ a)((((i ~> c) x)))
    ≡[ #2 it ]
      (i ~> c) x
    qed
  ren₂ (ι₁ i) (ι₂ b) (ι₁ k) x =
    let
      as = [ b ] ∪ Иe₁ (asupp x)
      a  = new as
      instance
        _ : a # x
        _ = Иe₂ (asupp x) a {{∉∪₂ (unfinite as)}}
        _ : a ≠ b
        _ = ∉[]₁ (∉∪₁ (unfinite as))
        _ : b ≠ a
        _ = symm≠ a b it
        _ : i ≠ k
        _ = ap≠ {A = ℕ} {ℕ𝔸} {ι₁} {i} {k} it
    in
    proof
      (i ~> b) ((i ↦ k) x)
    ≡[ ap (i ~> b) (↦fresh x a) ]
      (i ~> b)((k <~ a)((i ~> a)x))
    ≡[ oc₇ _ _ _ _ _ ]
      (k <~ a)((i ~> b)((i ~> a)x))
    ≡[ ap (k <~ a) (oc₁ _ _ _ _) ]
      (k <~ a)((i ~> a)x)
    ≡[ symm (↦fresh x a) ]
      (i ↦ k) x
    qed
  ren₂ (ι₁ _) (ι₂ _) (ι₂ _) _ = oc₁ _ _ _ _
  ren₂ (ι₂ _) (ι₁ _) (ι₁ _) _ = oc₂ _ _ _ _
  ren₂ (ι₂ a) (ι₁ j) (ι₂ c) x =
    let
      i = π₁ (isupp x)
      k = (max i j) +1
      k≻x : k ≻ x
      k≻x = ≻1 (≤trans ≤max₁ (≤+1 ≤refl)) (π₂ (isupp x))
      instance
        _ : a ≠ c
        _ = ap≠ {A = 𝔸} {ℕ𝔸} {ι₂} {a} {c} it
        _ : c ≠ a
        _ = symm≠ a c it
        _ : k ≠ j
        _ = +1≤→≠ j k (+1≤ ≤max₂)
    in
    proof
      (j <~ a)((c ↤ a)x)
    ≡[ ap (j <~ a) (↤fresh x k k≻x) ]
      (j <~ a)((k ~> c)((k <~ a)x))
    ≡[ symm (oc₇ _ _ _ _ _) ]
      (k ~> c)((j <~ a)((k <~ a)x))
    ≡[ ap (k ~> c) (oc₂ _ _ _ _) ]
      (k ~> c)((k <~ a)x)
    ≡[ symm (↤fresh x k k≻x) ]
      (c ↤ a)x
    qed
  ren₂ (ι₂ a) (ι₂ b) (ι₁ k) x =
    let
      i = π₁ (isupp ((k <~ a)x))
    in
    proof
      (b ↤ a)((k <~ a)x)
    ≡[]
      (i ~> b)((i <~ a)((k <~ a)x))
    ≡[ ap (i ~> b) (oc₂ _ _ _ _) ]
      (i ~> b)((k <~ a)x)
    ≡[ ≻3 (π₂ (isupp ((k <~ a)x))) ≤refl ]
      (k <~ a)x
    qed
  ren₂ (ι₂ a) (ι₂ b) (ι₂ c) x =
    let
      instance
        _ : a ≠ c
        _ = ap≠ {A = 𝔸} {ℕ𝔸} {ι₂} {a} {c} it
    in rn₂

  ren₃ :
    (a b c : ℕ𝔸)
    (x : X)
    → ---------------------------------------
    ren c b (ren b a x) ≡ ren c a (ren c b x)
  ren₃ (ι₁ i) (ι₁ j) (ι₁ k) x =
    let
      as = Иe₁ (asupp x)
      a  = new as
      bs = [ a ] ∪ as
      b  = new bs
      instance
        _ : a # x
        _ = Иe₂ (asupp x) a {{unfinite as}}
        _ : b # x
        _ = Иe₂ (asupp x) b {{∉∪₂ (unfinite bs)}}
        _ : b ≠ a
        _ =  ∉[]₁ (∉∪₁ (unfinite bs))
        _ : b # (i ↦ j)x
        _ = #<~ j b a _ {{#~> i b a x}}
        _ : a # (j ↦ k)x
        _ = oc₂ _ _ _ _
    in
    proof
      (j ↦ k)((i ↦ j)x)
    ≡[ ↦fresh ((i ↦ j)x) b ]
      (k <~ b)((j ~> b)((i ↦ j)x))
    ≡[]
      (k <~ b)((j ~> b)((j <~ a)((i ~> a)x)))
    ≡[ ap (k <~ b) (symm (oc₈ _ _ _ _ _)) ]
      (k <~ b)((i ~> b)((i <~ a)((j ~> b)x)))
    ≡[ symm (oc₉ _ _ _ _ _) ]
      (k <~ a)((i ~> a)((k <~ b)((j ~> b)x)))
    ≡[ ap ((k <~ a) ∘ (i ~> a)) (symm (↦fresh x b)) ]
      (k <~ a)((i ~> a)((j ↦ k)x))
    ≡[ symm (↦fresh ((j ↦ k)x) a) ]
      (i ↦ k)((j ↦ k)x)
    qed
  ren₃ (ι₁ i) (ι₁ j) (ι₂ c) x =
    let
      as = [ c ] ∪ Иe₁ (asupp x)
      a  = new as
      instance
        _ : a # x
        _ = Иe₂ (asupp x) a {{∉∪₂ (unfinite as)}}
        _ : a ≠ c
        _ = ∉[]₁ (∉∪₁ (unfinite as))
        _ : a # (j ~> c)x
        _ = #~> j a c x
    in
    proof
      (j ~> c)((i ↦ j)x)
    ≡[ ap (j ~> c) (↦fresh x a) ]
      (j ~> c)((j <~ a)((i ~> a)x))
    ≡[ symm (oc₈ _ _ _ _ _) ]
      (i ~> c)((i <~ a)((j ~> c)x))
    ≡[ ap (i ~> c) (#2 it) ]
      (i ~> c)((j ~> c)x)
    qed
  ren₃ (ι₁ i) (ι₂ b) (ι₁ k) x =
    let
      as = Иe₁ (asupp x)
      a  = new as
      instance
        _ : a # x
        _ = Иe₂ (asupp x) a {{unfinite as}}
        _ : a # (k <~ b)x
        _ = #<~ k a b x
    in
    proof
      (k <~ b)((i ~> b)x)
    ≡[ ap ((k <~ b) ∘ (i ~> b)) (symm (#2 it)) ]
      (k <~ b)((i ~> b)((i <~ a)x))
    ≡[ symm (oc₉ _ _ _ _ _) ]
      (k <~ a)((i ~> a)((k <~ b)x))
    ≡[ symm (↦fresh ((k <~ b)x) a) ]
      (i ↦ k)((k <~ b)x)
    qed
  ren₃ (ι₁ i) (ι₂ b) (ι₂ c) x with b ≐ c
  ... | equ =
    proof
      (b ↤ b)((i ~> b)x)
    ≡[ rn₁ ]
      (i ~> b)x
    ≡[ ap (i ~> b) (symm rn₁) ]
      (i ~> b)((b ↤ b)x)
    qed
  ... | neq f =
    let
      j = π₁ (isupp x)
      k = (max j i) +1
      k≻x : k ≻ x
      k≻x = ≻1 (≤trans ≤max₁ (≤+1 ≤refl)) (π₂ (isupp x))
      instance
        _ : i ≠ k
        _ = symm≠ k i (+1≤→≠ i k (+1≤ ≤max₂))
        _ : c ≠ b
        _ = symm≠ b c (¬≡→≠ f)
    in
    proof
      (c ↤ b)((i ~> b)x)
    ≡[ ↤fresh ((i ~> b) x) k (~>index-supports k≻x) ]
      (k ~> c)((k <~ b)((i ~> b)x))
    ≡[ symm (oc₈ _ _ _ _ _) ]
      (i ~> c)((i <~ b)((k ~> c)x))
    ≡[ ap ((i ~> c) ∘ (i <~ b)) (≻3 k≻x ≤refl) ]
      (i ~> c)((i <~ b)x)
    ≡[ ap ((i ~> c) ∘ (i <~ b)) (symm (≻3 k≻x ≤refl)) ]
      (i ~> c)((i <~ b)((k ~> b)x))
    ≡[ symm (oc₈ _ _ _ _ _) ]
      (k ~> c)((k <~ b)((i ~> c)x))
    ≡[ ap (k ~> c) (symm (oc₇ _ _ _ _ _)) ]
      (k ~> c)((i ~> c)((k <~ b)x))
    ≡[ symm (oc₅ _ _ _ _ _) ]
      (i ~> c)((k ~> c)((k <~ b)x))
    ≡[ ap (i ~> c) (symm (↤fresh x k k≻x)) ]
      (i ~> c)((c ↤ b)x)
    qed
  ren₃ (ι₂ a) (ι₁ j) (ι₁ k) x with k ≐ j
  ... | equ =
    proof
      (k ↦ k)((k <~ a)x)
    ≡[ ren₁ (ι₁ k) _ ]
      (k <~ a)x
    ≡[ ap (k <~ a) (symm (ren₁ (ι₁ k) _)) ]
      (k <~ a)((k ↦ k)x)
    qed
  ... | neq f =
    let
      bs = [ a ] ∪ Иe₁ (asupp x)
      b  = new bs
      instance
        _ : b # x
        _ = Иe₂ (asupp x) b {{∉∪₂ (unfinite bs)}}
        _ : b ≠ a
        _ = ∉[]₁ (∉∪₁ (unfinite bs))
        _ : k ≠ j
        _ = ¬≡→≠ f
        _ : j ≠ k
        _ = symm≠ k j it
        _ : b # (j <~ a)x
        _ = #<~ j b a x
    in
    proof
      (j ↦ k)((j <~ a)x)
    ≡[ ↦fresh _ _ ]
      (k <~ b)((j ~> b)((j <~ a)x))
    ≡[ symm (oc₉ _ _ _ _ _) ]
      (k <~ a)((j ~> a)((k <~ b)x))
    ≡[ ap ((k <~ a) ∘ (j ~> a)) (#2 it) ]
      (k <~ a)((j ~> a)x)
    ≡[ ap ((k <~ a) ∘ (j ~> a)) (symm (#2 it)) ]
      (k <~ a)((j ~> a)((j <~ b)x))
    ≡[ symm (oc₉ _ _ _ _ _) ]
      (k <~ b)((j ~> b)((k <~ a)x))
    ≡[ ap (k <~ b) (oc₇ _ _ _ _ _ ) ]
      (k <~ b)((k <~ a)((j ~> b)x))
    ≡[ oc₆ _ _ _ _ _ ]
      (k <~ a)((k <~ b)((j ~> b)x))
    ≡[ ap (k <~ a) (symm (↦fresh _ _)) ]
      (k <~ a)((j ↦ k)x)
    qed
  ren₃ (ι₂ a) (ι₁ j) (ι₂ c) x =
    let
      i = π₁ (isupp x)
      i≻x : i ≻ x
      i≻x =  π₂ (isupp x)
    in
    proof
      (j ~> c)((j <~ a)x)
    ≡[ ap ((j ~> c) ∘ (j <~ a)) (symm (≻3 i≻x ≤refl)) ]
      (j ~> c)((j <~ a)((i ~> a)x))
    ≡[ symm (oc₈ _ _ _ _ _) ]
      (i ~> c)((i <~ a)((j ~> c)x))
    ≡[ symm (↤fresh _ _ (~>index-supports i≻x)) ]
      (c ↤ a)((j ~> c)x)
    qed
  ren₃ (ι₂ a) (ι₂ b) (ι₁ k) x =
    let
      i = π₁ (isupp x)
      i≻x : i ≻ x
      i≻x =  π₂ (isupp x)
      j = max i (k +1)
      j≻x : j ≻ x
      j≻x = ≻1 ≤max₁ i≻x
    in
    proof
      (k <~ b)((b ↤ a)x)
    ≡[ ap (k <~ b) (↤fresh _ _ j≻x) ]
      (k <~ b)((j ~> b)((j <~ a)x))
    ≡[ symm (oc₉ _ _ _ _ _) ]
      (k <~ a)((j ~> a)((k <~ b)x))
    ≡[ ap (k <~ a) (≻3 (<~index-supports i≻x) ≤refl) ]
      (k <~ a)((k <~ b)x)
    qed
  ren₃ (ι₂ _) (ι₂ _) (ι₂ _) _ = rn₃

  ren₄ :
    (a b c d : ℕ𝔸)
    (x : X)
    {{_ : b ≠ c}}
    {{_ : a ≠ c}}
    {{_ : d ≠ a}}
    → ---------------------------------------
    ren b a (ren d c x) ≡ ren d c (ren b a x)
  ren₄ (ι₁ i) (ι₁ j) (ι₁ k) (ι₁ l) x =
      let
      as = Иe₁ (asupp x)
      a  = new as
      bs = [ a ] ∪ as
      b  = new bs
      instance
        _ : a # x
        _ = Иe₂ (asupp x) a {{unfinite as}}
        _ : b # x
        _ = Иe₂ (asupp x) b {{∉∪₂ (unfinite bs)}}
        _ : b ≠ a
        _ =  ∉[]₁ (∉∪₁ (unfinite bs))
        _ : a ≠ b
        _ = symm≠ b a it
        _ : b # (k ↦ l)x
        _ = #<~ l b a _ {{#~> k b a x}}
        _ : a # (i ↦ j)x
        _ = oc₂ _ _ _ _
      instance
        _ : l ≠ i
        _ = ap≠ {A = ℕ} {ℕ𝔸} {ι₁} {l} {i} it
        _ : i ≠ l
        _ = symm≠ l i it
        _ : j ≠ k
        _ = ap≠ {A = ℕ} {ℕ𝔸} {ι₁} {j} {k} it
        _ : k ≠ j
        _ = symm≠ j k it
        _ : i ≠ k
        _ = ap≠ {A = ℕ} {ℕ𝔸} {ι₁} {i} {k} it
    in
    proof
      (i ↦ j)((k ↦ l)x)
    ≡[ ↦fresh _ b ]
      (j <~ b)((i ~> b)((k ↦ l)x))
    ≡[]
      (j <~ b)((i ~> b)((l <~ a)((k ~> a)x)))
    ≡[ ap (j <~ b) (oc₇ _ _ _ _ _) ]
      (j <~ b)((l <~ a)((i ~> b)((k ~> a)x)))
    ≡[ oc₆ _ _ _ _ _ ]
      (l <~ a)((j <~ b)((i ~> b)((k ~> a)x)))
    ≡[ ap ((l <~ a) ∘ (j <~ b)) (oc₅ _ _ _ _ _) ]
      (l <~ a)((j <~ b)((k ~> a)((i ~> b)x)))
    ≡[ ap (l <~ a) (symm(oc₇ _ _ _ _ _)) ]
      (l <~ a)((k ~> a)((j <~ b)((i ~> b)x)))
    ≡[ ap ((l <~ a) ∘ (k ~> a)) (symm (↦fresh _ b)) ]
      (l <~ a)((k ~> a)((i ↦ j)x))
    ≡[ symm (↦fresh _ a) ]
      (k ↦ l)((i ↦ j)x)
    qed
  ren₄ (ι₁ i) (ι₁ j) (ι₁ k) (ι₂ d) x =
    let
      as = [ d ] ∪ Иe₁ (asupp x)
      a  = new as
      instance
        _ : a # x
        _ = Иe₂ (asupp x) a {{∉∪₂ (unfinite as)}}
        _ : a ≠ d
        _ = ∉[]₁ (∉∪₁ (unfinite as))
        _ : d ≠ a
        _ = symm≠ a d it
        _ : a # (k ~> d)x
        _ = #~> k a d x
        _ : i ≠ k
        _ = ap≠ {A = ℕ} {ℕ𝔸} {ι₁} {i} {k} it
        _ : k ≠ j
        _ = symm≠ j k (ap≠ {A = ℕ} {ℕ𝔸} {ι₁} {j} {k} it)
    in
    proof
      (i ↦ j)((k ~> d)x)
    ≡[ ↦fresh _ _ ]
      (j <~ a)((i ~> a)((k ~> d)x))
    ≡[ ap (j <~ a) (oc₅ _ _ _ _ _) ]
      (j <~ a)((k ~> d)((i ~> a)x))
    ≡[ symm (oc₇ _ _ _ _ _) ]
      (k ~> d)((j <~ a)((i ~> a)x))
    ≡[ ap (k ~> d) (symm (↦fresh _ _)) ]
      (k ~> d)((i ↦ j)x)
    qed
  ren₄ (ι₁ i) (ι₁ j) (ι₂ c) (ι₁ l) x =
    let
      as = [ c ] ∪ Иe₁ (asupp x)
      a  = new as
      instance
        _ : a # x
        _ = Иe₂ (asupp x) a {{∉∪₂ (unfinite as)}}
        _ : a ≠ c
        _ = ∉[]₁ (∉∪₁ (unfinite as))
        _ : a # (l <~ c)x
        _ = #<~ l a c x
        _ : i ≠ l
        _ = symm≠ l i (ap≠ {A = ℕ} {ℕ𝔸} {ι₁} {l} {i} it)
    in
    proof
      (i ↦ j)((l <~ c)x)
    ≡[ ↦fresh _ _ ]
      (j <~ a)((i ~> a)((l <~ c)x))
    ≡[ ap (j <~ a) (oc₇ _ _ _ _ _) ]
      (j <~ a)((l <~ c)((i ~> a)x))
    ≡[ oc₆ _ _ _ _ _ ]
      (l <~ c)((j <~ a)((i ~> a)x))
    ≡[ ap (l <~ c) (symm (↦fresh _ _)) ]
      (l <~ c)((i ↦ j)x)
    qed
  ren₄ (ι₁ i) (ι₁ j) (ι₂ c) (ι₂ d) x =
    let
      as' = Иe₁ (asupp x)
      a'  = new as'
      as = [ c ] ∪ [ d ] ∪ as'
      a  = new as
      k = π₁ (isupp x)
      k≻x : k ≻ x
      k≻x = π₂ (isupp x)
      l = (max (max i j) k) +1
      l≻x : l ≻ x
      l≻x = ≻1 (≤trans ≤max₂ (≤+1 ≤refl)) k≻x
      k≻~>a'x : k ≻ (i ~> a')x
      k≻~>a'x = ~>index-supports k≻x
      k' = max k (j +1)
      k'≻i↦jx : k' ≻ (i ↦ j)x
      k'≻i↦jx = <~index-supports k≻~>a'x
      l≥k' : l ≥ k'
      l≥k' = ≤lub k (j +1) l
        (≤trans ≤max₂ (≤+1 ≤refl))
        (+1≤ (≤trans ≤max₂ (≤max₁ {y = k})))
      l≻i↦jx : l ≻ (i ↦ j)x
      l≻i↦jx = ≻1 l≥k' k'≻i↦jx
      instance
        _ : a # x
        _ = Иe₂ (asupp x) a {{∉∪₂ (∉∪₂ (unfinite as))}}
        _ : a ≠ d
        _ = ∉[]₁ (∉∪₁ (∉∪₂(unfinite as)))
        _ : d ≠ a
        _ = symm≠ a d it
        _ : a # (d ↤ c)x
        _ = #~> k a d _ {{#<~ k a c x}}
        _ : a ≠ c
        _ = ∉[]₁ (∉∪₁ (unfinite as))
        _ : l ≠ j
        _ = +1≤→≠ j l (+1≤ (≤trans ≤max₂ (≤max₁{y = k})))
        _ : i ≠ l
        _ = symm≠ l i (+1≤→≠ i l (+1≤ (≤trans ≤max₁ (≤max₁{y = k}))))
    in
    proof
      (i ↦ j)((d ↤ c)x)
    ≡[ ↦fresh _ _ ]
      (j <~ a)((i ~> a)((d ↤ c)x))
    ≡[ ap ((j <~ a) ∘ (i ~> a)) (↤fresh _ _ l≻x) ]
      (j <~ a)((i ~> a)((l ~> d)((l <~ c)x)))
    ≡[ ap (j <~ a) (oc₅ _ _ _ _ _) ]
      (j <~ a)((l ~> d)((i ~> a)((l <~ c)x)))
    ≡[ symm (oc₇ _ _ _ _ _) ]
      (l ~> d)((j <~ a)((i ~> a)((l <~ c)x)))
    ≡[ ap ((l ~> d) ∘ (j <~ a)) (oc₇ _ _ _ _ _) ]
      (l ~> d)((j <~ a)((l <~ c)((i ~> a)x)))
    ≡[ ap  (l ~> d) (oc₆ _ _ _ _ _) ]
      (l ~> d)((l <~ c)((j <~ a)((i ~> a)x)))
    ≡[ ap ((l ~> d) ∘ (l <~ c)) (symm (↦fresh _ _)) ]
      (l ~> d)((l <~ c)((i ↦ j)x))
    ≡[ symm (↤fresh _ _ l≻i↦jx) ]
      (d ↤ c)((i ↦ j)x)
    qed
  ren₄ (ι₁ i) (ι₂ b) (ι₁ k) (ι₁ l) x =
    let
      as = [ b ] ∪ Иe₁ (asupp x)
      a  = new as
      instance
        _ : a # x
        _ = Иe₂ (asupp x) a {{∉∪₂ (unfinite as)}}
        _ : a ≠ b
        _ = ∉[]₁ (∉∪₁ (unfinite as))
        _ : b ≠ a
        _ = symm≠ a b it
        _ : i ≠ k
        _ = ap≠ {A = ℕ} {ℕ𝔸} {ι₁} {i} {k} it
        _ : i ≠ l
        _ = symm≠ l i (ap≠ {A = ℕ} {ℕ𝔸} {ι₁} {l} {i} it)
        _ : a # (i ~> b)x
        _ = #~> i a b x
    in
    proof
      (i ~> b)((k ↦ l)x)
    ≡[ ap (i ~> b) (↦fresh _ _) ]
      (i ~> b)((l <~ a)((k ~> a)x))
    ≡[ oc₇ _ _ _ _ _ ]
      (l <~ a)((i ~> b)((k ~> a)x))
    ≡[ ap (l <~ a) (oc₅ _ _ _ _ _) ]
      (l <~ a)((k ~> a)((i ~> b)x))
    ≡[ symm (↦fresh _ _) ]
      (k ↦ l) ((i ~> b) x)
    qed
  ren₄ (ι₁ i) (ι₂ b) (ι₁ k) (ι₂ d) x =
    let
      instance
        _ : i ≠ k
        _ = ap≠ {A = ℕ} {ℕ𝔸} {ι₁} {i} {k} it
    in oc₅ _ _ _ _ _
  ren₄ (ι₁ i) (ι₂ b) (ι₂ c) (ι₁ l) x =
    let
      instance
        _ : i ≠ l
        _ = symm≠ l i (ap≠ {A = ℕ} {ℕ𝔸} {ι₁} {l} {i} it)
        _ : b ≠ c
        _ = ap≠ {A = 𝔸} {ℕ𝔸} {ι₂} {b} {c} it
    in oc₇ _ _ _ _ _
  ren₄ (ι₁ i) (ι₂ b) (ι₂ c) (ι₂ d) x =
    let
      j = π₁ (isupp x)
      k = (max i j) +1
      k≻x : k ≻ x
      k≻x = ≻1 (≤trans ≤max₂ (≤+1 ≤refl)) (π₂ (isupp x))
      k≻i~>bx : k ≻ (i ~> b)x
      k≻i~>bx = ~>index-supports k≻x
      instance
        _ : i ≠ k
        _ = symm≠ k i (+1≤→≠ i k (+1≤ ≤max₁))
        _ : b ≠ c
        _ = ap≠ {A = 𝔸} {ℕ𝔸} {ι₂} {b} {c} it
    in
    proof
      (i ~> b)((d ↤ c)x)
    ≡[ ap (i ~> b) (↤fresh _ _ k≻x) ]
      (i ~> b)((k ~> d)((k <~ c)x))
    ≡[ oc₅ _ _ _ _ _ ]
      (k ~> d)((i ~> b)((k <~ c)x))
    ≡[ ap (k ~> d) (oc₇ _ _ _ _ _) ]
      (k ~> d)((k <~ c)((i ~> b)x))
    ≡[ symm (↤fresh _ _ k≻i~>bx) ]
      (d ↤ c)((i ~> b)x)
    qed
  ren₄ (ι₂ a) (ι₁ j) (ι₁ k) (ι₁ l) x =
    let
      bs = [ a ] ∪ Иe₁ (asupp x)
      b  = new bs
      instance
        _ : b # x
        _ = Иe₂ (asupp x) b {{∉∪₂ (unfinite bs)}}
        _ : b ≠ a
        _ = ∉[]₁ (∉∪₁ (unfinite bs))
        _ : a ≠ b
        _ = symm≠ b a it
        _ : k ≠ j
        _ = symm≠ j k (ap≠ {A = ℕ} {ℕ𝔸} {ι₁} {j} {k} it)
        _ : b # (j <~ a)x
        _ = #<~ j b a x
    in
    proof
      (j <~ a)((k ↦ l) x)
    ≡[ ap (j <~ a) (↦fresh _ _) ]
      (j <~ a)((l <~ b)((k ~> b)x))
    ≡[ oc₆ _ _ _ _ _ ]
      (l <~ b)((j <~ a)((k ~> b)x))
    ≡[ ap (l <~ b) (symm (oc₇ _ _ _ _ _)) ]
      (l <~ b)((k ~> b)((j <~ a)x))
    ≡[ symm (↦fresh _ _) ]
      (k ↦ l)((j <~ a) x)
    qed
  ren₄ (ι₂ a) (ι₁ j) (ι₁ k) (ι₂ d) x =
    let
      instance
        _ : k ≠ j
        _ = symm≠ j k (ap≠ {A = ℕ} {ℕ𝔸} {ι₁} {j} {k} it)
        _ : d ≠ a
        _ = ap≠ {A = 𝔸} {ℕ𝔸} {ι₂} {d} {a} it
    in symm (oc₇ _ _ _ _ _)
  ren₄ (ι₂ a) (ι₁ j) (ι₂ c) (ι₁ l) x =
    let
      instance
        _ : a ≠ c
        _ = ap≠ {A = 𝔸} {ℕ𝔸} {ι₂} {a} {c} it
    in oc₆ _ _ _ _ _
  ren₄ (ι₂ a) (ι₁ j) (ι₂ c) (ι₂ d) x =
    let
      i = π₁ (isupp x)
      i≻x : i ≻ x
      i≻x = π₂ (isupp x)
      k = (max i j) +1
      k≻x : k ≻ x
      k≻x = ≻1 (≤trans ≤max₁ (≤+1 ≤refl)) i≻x
      k' = max i (j +1)
      k'≻j<~ax  : k' ≻ (j <~ a) x
      k'≻j<~ax = <~index-supports i≻x
      k≻j<~ax : k ≻ (j <~ a)x
      k≻j<~ax =  ≻1 (≤lub i (j +1) k
        (≤trans ≤max₁ (≤+1 ≤refl))
        (+1≤ ≤max₂)) k'≻j<~ax
      instance
        _ : k ≠ j
        _ = +1≤→≠ j k (+1≤ ≤max₂)
        _ : d ≠ a
        _ = ap≠ {A = 𝔸} {ℕ𝔸} {ι₂} {d} {a} it
        _ : a ≠ c
        _ = ap≠ {A = 𝔸} {ℕ𝔸} {ι₂} {a} {c} it
    in
    proof
      (j <~ a)((d ↤ c)x)
    ≡[ ap (j <~ a) (↤fresh _ _ k≻x) ]
      (j <~ a)((k ~> d)((k <~ c)x))
    ≡[ symm (oc₇ _ _ _ _ _) ]
      (k ~> d)((j <~ a)((k <~ c)x))
    ≡[ ap (k ~> d) (oc₆ _ _ _ _ _) ]
      (k ~> d)((k <~ c)((j <~ a)x))
    ≡[ symm (↤fresh _ _ k≻j<~ax) ]
      (d ↤ c)((j <~ a)x)
    qed
  ren₄ (ι₂ a) (ι₂ b) (ι₁ k) (ι₁ l) x =
    let
      cs' = Иe₁ (asupp x)
      c'  = new cs'
      i = π₁ (isupp x)
      i≻x : i ≻ x
      i≻x = π₂ (isupp x)
      i≻k~>c'x : i ≻ (k ~> c')x
      i≻k~>c'x = ~>index-supports i≻x
      j = (max i (max k l)) +1
      j≻x : j ≻ x
      j≻x = ≻1 (≤trans ≤max₁ (≤+1 ≤refl)) i≻x
      i' = max i (l +1)
      i'≻k↦lx : i' ≻ (k ↦ l)x
      i'≻k↦lx  = <~index-supports i≻k~>c'x
      j≥i' : j ≥ i'
      j≥i' = ≤lub i (l +1) j
        (≤trans ≤max₁ (≤+1 ≤refl))
        (+1≤ (≤trans ≤max₂ (≤max₂{x = i})))
      j≻k↦lx : j ≻ (k ↦ l)x
      j≻k↦lx = ≻1 j≥i' i'≻k↦lx
      cs = [ a ] ∪ [ b ] ∪ Иe₁ (asupp x)
      c  = new cs
      instance
        _ : c # x
        _ = Иe₂ (asupp x) c {{∉∪₂ (∉∪₂(unfinite cs))}}
        _ : c ≠ a
        _ = ∉[]₁ (∉∪₁ (unfinite cs))
        _ : a ≠ c
        _ = symm≠ c a it
        _ : c ≠ b
        _ = ∉[]₁ (∉∪₁ (∉∪₂ (unfinite cs)))
        _ : b ≠ c
        _ = symm≠ c b it
        _ : j ≠ l
        _ = +1≤→≠ l j (+1≤ (≤trans ≤max₂ (≤max₂ {x = i})))
        _ : j ≠ k
        _ = +1≤→≠ k j (+1≤ (≤trans ≤max₁ (≤max₂ {x = i})))
        _ : k ≠ j
        _ = symm≠ j k it
        _ : c # (b ↤ a)x
        _ = #~> i c b _ {{#<~ i c a x}}
    in
    proof
      (b ↤ a)((k ↦ l)x)
    ≡[ ↤fresh _ _ j≻k↦lx ]
      (j ~> b)((j <~ a)((k ↦ l)x))
    ≡[ ap ((j ~> b) ∘ (j <~ a)) (↦fresh _ _) ]
      (j ~> b)((j <~ a)((l <~ c)((k ~> c)x)))
    ≡[ ap (j ~> b) (oc₆ _ _ _ _ _) ]
      (j ~> b)((l <~ c)((j <~ a)((k ~> c)x)))
    ≡[ oc₇ _ _ _ _ _ ]
      (l <~ c)((j ~> b)((j <~ a)((k ~> c)x)))
    ≡[ ap ((l <~ c) ∘ (j ~> b)) (symm (oc₇ _ _ _ _ _)) ]
      (l <~ c)((j ~> b)((k ~> c)((j <~ a)x)))
    ≡[ ap (l <~ c) (oc₅ _ _ _ _ _) ]
      (l <~ c)((k ~> c)((j ~> b)((j <~ a)x)))
    ≡[ ap ((l <~ c) ∘ (k ~> c)) (symm (↤fresh _ _ j≻x)) ]
      (l <~ c)((k ~> c)((b ↤ a)x))
    ≡[ symm (↦fresh _ _) ]
      (k ↦ l)((b ↤ a)x)
    qed
  ren₄ (ι₂ a) (ι₂ b) (ι₁ k) (ι₂ d) x =
    let
      i = π₁ (isupp x)
      i≻x : i ≻ x
      i≻x = π₂ (isupp x)
      j = (max i k) +1
      j≻x : j ≻ x
      j≻x = ≻1 (≤trans ≤max₁ (≤+1 ≤refl)) i≻x
      j≻k~>dx : j ≻ (k ~> d)x
      j≻k~>dx = ~>index-supports j≻x
      instance
        _ : d ≠ a
        _ = ap≠ {A = 𝔸} {ℕ𝔸} {ι₂} {d} {a} it
        _ : j ≠ k
        _ = +1≤→≠ k j (+1≤ ≤max₂)
        _ : k ≠ j
        _ = symm≠ j k it
    in
    proof
      (b ↤ a)((k ~> d)x)
    ≡[ ↤fresh _ _ j≻k~>dx ]
      (j ~> b)((j <~ a)((k ~> d)x))
    ≡[ ap (j ~> b) (symm (oc₇ _ _ _ _ _)) ]
      (j ~> b)((k ~> d)((j <~ a)x))
    ≡[ oc₅ _ _ _ _ _ ]
      (k ~> d)((j ~> b)((j <~ a)x))
    ≡[ ap (k ~> d) (symm (↤fresh _ _ j≻x)) ]
      (k ~> d)((b ↤ a)x)
    qed
  ren₄ (ι₂ a) (ι₂ b) (ι₂ c) (ι₁ l) x =
    let
      i = π₁ (isupp x)
      i≻x : i ≻ x
      i≻x = π₂ (isupp x)
      j = (max i l) +1
      j≻x : j ≻ x
      j≻x = ≻1 (≤trans ≤max₁ (≤+1 ≤refl)) i≻x
      j≻l<~cx : j ≻ (l <~ c)x
      j≻l<~cx = ≻1 (≤lub i (l +1) j
        (≤trans ≤max₁ (≤+1 ≤refl)) (+1≤ ≤max₂))
        (<~index-supports i≻x)
      instance
        _ : a ≠ c
        _ = ap≠ {A = 𝔸} {ℕ𝔸} {ι₂} {a} {c} it
        _ : b ≠ c
        _ = ap≠ {A = 𝔸} {ℕ𝔸} {ι₂} {b} {c} it
        _ : j ≠ l
        _ = +1≤→≠ l j (+1≤ ≤max₂)
    in
    proof
      (b ↤ a)((l <~ c)x)
    ≡[ ↤fresh _ _ j≻l<~cx ]
      (j ~> b)((j <~ a)((l <~ c)x))
    ≡[ ap (j ~> b) (oc₆ _ _ _ _ _) ]
      (j ~> b)((l <~ c)((j <~ a)x))
    ≡[ oc₇ _ _ _ _ _ ]
      (l <~ c)((j ~> b)((j <~ a)x))
    ≡[ ap (l <~ c) (symm ( ↤fresh _ _ j≻x)) ]
      (l <~ c)((b ↤ a)x)
    qed
  ren₄ (ι₂ a) (ι₂ b) (ι₂ c) (ι₂ d) x =
    let
      instance
        _ : a ≠ c
        _ = ap≠ {A = 𝔸} {ℕ𝔸} {ι₂} {a} {c} it
        _ : b ≠ c
        _ = ap≠ {A = 𝔸} {ℕ𝔸} {ι₂} {b} {c} it
        _ : d ≠ a
        _ = ap≠ {A = 𝔸} {ℕ𝔸} {ι₂} {d} {a} it
    in rn₄

-- Now we show that the ℕ𝔸-renset associated with a locally nameless set
-- is in fact finitely suppported
lns→fsRenset :
  {X : Set}
  {{_ : lns X}}
  → ------------
  fsRenset{ℕ𝔸} X
renset {{lns→fsRenset}} = lns→Renset
rsupp  {{lns→fsRenset{X}}} x = Иi и₁ и₂
  where
  instance
    _ : Renset X
    _ = lns→Renset
  и₁ : Fset ℕ𝔸
  и₁ = Fset′ ι₁ (ordinal (π₁ (isupp x))) ∪ Fset′ ι₂ (Иe₁ (asupp x))

  ≻→ι₁♯ : ∀ i → i ≻ x → ι₁ i ♯ x
  ≻→ι₁♯ i p = Иi Ø f
    where
    f :
      (na : ℕ𝔸)
      {{_ : na ∉ Ø}}
      → ---------------
      ρ na (ι₁ i )x ≡ x
    f (ι₁ j) = ≻↦ i j x p
    f (ι₂ b) = ≻3 p ≤refl

  #→ι₂♯ : ∀ a → {{_ : a # x}} → ι₂ a ♯ x
  #→ι₂♯ a = Иi Ø f
    where
    f :
      (na : ℕ𝔸)
      {{_ : na ∉ Ø}}
      → ---------------
      ρ na (ι₂ a) x ≡ x
    f (ι₁ j) = #2 it
    f (ι₂ b) = #→ren# it b

  и₂ :
    (na : ℕ𝔸)
    {{_ : na ∉ и₁}}
    → -------------
    na ♯ x
  и₂ (ι₁ i) {{∉∪}} =
    ≻→ι₁♯ i (≻1 (∉ordinal→≥ _ _ Fset′∉) (π₂ (isupp x)))
  и₂ (ι₂ a) {{∉∪}} =
    #→ι₂♯ a {{Иe₂ (asupp x) a {{Fset′∉}}}}
