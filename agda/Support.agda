module Support where

open import Prelude
open import Unfinite
open import oc-Sets
open import Freshness
open import LocalClosedness

----------------------------------------------------------------------
-- Locally nameless sets [Definition 2.9]
----------------------------------------------------------------------
record lns (X : Set) : Set where
  constructor mklns
  field
    {{ocSet}} : oc X
    asupp : (x : X) → И a ∶ 𝔸 , a # x
    isupp : (x : X) → ∑ i ∶ ℕ , i ≻ x

open lns{{...}} public

infix 4 _atom-supports_
_atom-supports_ :
  {X : Set}
  {{_ : oc X}}
  (A : Fset 𝔸)
  (x : X)
  → ----------
  Set
A atom-supports x = ∀ a → a ∉ A → a # x

----------------------------------------------------------------------
-- Locally nameless set of indices and atoms [Example 2.10]
----------------------------------------------------------------------
instance
  lnsℕ𝔸 : lns ℕ𝔸
  ocSet {{lnsℕ𝔸}} = ocℕ𝔸
  asupp {{lnsℕ𝔸}} (ι₁ i) = Иi Ø λ _ → refl
  asupp {{lnsℕ𝔸}} (ι₂ a) = Иi [ a ] и₂
    where
    и₂ : (b : 𝔸){{_ : b ∉ [ a ]}} → b # ι₂ a
    и₂ b {{∉[]{{p}}}} rewrite p = refl
  isupp {{lnsℕ𝔸}} (ι₁ i) = (i +1 , s₂)
    where
    s₂ : i +1 ≻ ι₁ i
    s₂ j {{p}} rewrite +1≤→≠ i j p = (new Ø , refl)
  isupp {{lnsℕ𝔸}} (ι₂ a) = (0 , λ _ → (a , refl))

----------------------------------------------------------------------
-- Properties of open/close operations wrt freshness [Lemma 2.12]
----------------------------------------------------------------------
module _
  {X : Set}
  {{_ : oc X}}
  {i : ℕ}
  {a : 𝔸}
  {A : Fset 𝔸}
  {x : X}
  (f : A atom-supports x)
  where
  ~>atom-supports : A ∪ [ a ] atom-supports (i ~> a)x
  ~>atom-supports b (∉∪{{_}}{{∉[]}}) =
    #1 {i = i +1}{0}
    (proof
       ((i +1) <~ b) ((i ~> a) x)
     ≡[ symm (oc₇ i (i +1) a b x {{ ≠+1 i}} {{symm≠ b a it}}) ]
       (i ~> a) ((i +1 <~ b)x)
     ≡[ ap (i ~> a) (#1 {j = i +1} (f b it)) ]
       (i ~> a) x
     qed)

  <~atom-supports : A -[ a ] atom-supports (i <~ a)x
  <~atom-supports b p with b ≐ a
  ... | neq g =
    proof
      (0 <~ b) ((i <~ a) x)
    ≡[ oc₆ 0 i b a x {{¬≡→≠ g}} ]
      (i <~ a) ((0 <~ b)x)
    ≡[ ap (i <~ a) (f b (∉-[] p (¬≡→≠ g))) ]
      (i <~ a) x
    qed
  ... | equ = oc₂ 0 i b x

#<~ :
  {X : Set}
  {{_ : lns X}}
  (i : ℕ)
  (a b : 𝔸)
  (x : X)
  {{_ : a # x}}
  → -----------
  a # (i <~ b)x
#<~ i a b x with a ≐ b
... | equ = oc₂ _ _ _ _
... | neq f =
  proof
    (0 <~ a) ((i <~ b) x)
  ≡[ oc₆ _ _ _ _ _ {{¬≡→≠ f}} ]
    (i <~ b) ((0 <~ a) x)
  ≡[ ap (i <~ b) (#2 it) ]
    (i <~ b)x
  qed

#~> :
  {X : Set}
  {{_ : lns X}}
  (i : ℕ)
  (a b : 𝔸)
  (x : X)
  {{_ : a # x}}
  {{_ : a ≠ b}}
  → -----------
  a # (i ~> b)x
#~> i a b x = #3 {i = i +1}
  (proof
     (i +1 <~ a)((i ~> b)x)
   ≡[ symm (oc₇ _ _ _ _ _ {{≠+1 i}}{{symm≠ a b it}}) ]
     (i ~> b)((i +1 <~ a)x)
   ≡[ ap (i ~> b) (#2 it) ]
     (i ~> b)x
   qed)


----------------------------------------------------------------------
-- Properties of open/close operations wrt local closure [Lemma 2.13]
----------------------------------------------------------------------
module _
  {X : Set}
  {{_ : oc X}}
  {i : ℕ}
  {a : 𝔸}
  {x : X}
  where
  ~>index-supports : -- Equation (10)
    {j : ℕ}
    (_ : j ≻ x)
    → -----------
    j ≻ (i ~> a)x
  ~>index-supports p k with k ≐ i
  ... | neq f = (a ,
    (proof
       (k ~> a)((i ~> a) x)
     ≡[ oc₅ _ _ _ _ _ {{¬≡→≠ f}} ]
       (i ~> a)((k ~> a) x)
     ≡[ ap (i ~> a) (≻3 p it) ]
       (i ~> a) x
     qed))
  ... | equ = (a , oc₁ _ _ _ _)

  ~>index-supports' : -- Equation (11)
    i +1 ≻ x → i ≻ (i ~> a) x
  ~>index-supports' p j with j ≐ i
  ... | neq f = (a ,
    (proof
       (j ~> a)((i ~> a) x)
     ≡[ oc₅ _ _ _ _ _ {{¬≡→≠ f}}  ]
       (i ~> a) ((j ~> a) x)
     ≡[ ap (i ~> a) (≻3 p (≤≠ it (symm≠ j i (¬≡→≠ f)))) ]
       (i ~> a) x
     qed))
  ... | equ = (a , oc₁ _ _ _ _)

  <~index-supports : -- Equation (12)
    {j : ℕ}
    (_ : j ≻ x)
    → ------------------------
    max j (i +1) ≻ (i <~ a) x
  <~index-supports p k with (b , ∉[]) ← fresh{𝔸} [ a ] =
    (b ,
      (proof
        (k ~> b)((i <~ a) x)
      ≡[ oc₇ _ _ _ _ _ {{+1≤→≠ i k (≤trans ≤max₂ it)}} ]
        (i <~ a)((k ~> b) x)
      ≡[ ap (i <~ a) (≻3 p (≤trans ≤max₁ it)) ]
        (i <~ a) x
      qed))
