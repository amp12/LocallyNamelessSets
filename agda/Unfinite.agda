module Unfinite where

open import Prelude

----------------------------------------------------------------------
-- The property of being an unfinite set
----------------------------------------------------------------------
record Unfinite {l : Level}(A : Set l) : Set l where
  field
    {{deceq}} : hasDecEq A
    new       : Fset A → A
    unfinite  : (xs : Fset A) → new xs ∉ xs

open Unfinite{{...}} public

----------------------------------------------------------------------
-- ℕ is unfinite
----------------------------------------------------------------------
instance
  Unifiniteℕ : Unfinite ℕ
  deceq    {{Unifiniteℕ}}    = hasDecEqℕ
  new      {{Unifiniteℕ}} xs = maxfs xs +1
  unfinite {{Unifiniteℕ}}    = maxfs+1∉

----------------------------------------------------------------------
-- Unfinite disjoint union
----------------------------------------------------------------------
Unfinite⊎ :
  {l : Level}
  {A B : Set l}
  {{_ : hasDecEq A}}
  {{_ : Unfinite B}}
  → ----------------
  Unfinite (A ⊎ B)
deceq    {{Unfinite⊎}}    = hasDecEq⊎
new      {{Unfinite⊎}} xs = ι₂ (new (ι₂⁻¹ xs))
unfinite {{Unfinite⊎}} xs =
  ∉ι₂⁻¹→ι₂∉ xs (new (ι₂⁻¹ xs)) (unfinite (ι₂⁻¹ xs))

----------------------------------------------------------------------
-- Supported sets over a given unfinite set
----------------------------------------------------------------------
record Supp {V : Set}{{_ : Unfinite V}}(S : Set) : Set where
  field
    § : S → Fset V

open Supp{{...}} public

{-# DISPLAY Supp.§ _ s = § s #-}

instance
  SuppV : {V : Set}{{_ : Unfinite V}} → Supp V
  § {{SuppV}} x = [ x ]

  SuppFsetV : {V : Set}{{_ : Unfinite V}} → Supp (Fset V)
  § {{SuppFsetV}} xs = xs

  Supp× :
    {V : Set}
    {{_ : Unfinite V}}
    {S S' : Set}
    {{_ : Supp{V} S}}
    {{_ : Supp{V} S'}}
    → ----------------
    Supp{V} (S × S')
  § {{Supp×}} (s , s') = § s ∪ § s'

fresh :
  {V : Set}
  {{_ : Unfinite V}}
  {S : Set}
  {{_ : Supp S}}
  (s : S)
  → ---------------
  ∑ u ∶ V , u ∉ § s
fresh s = (new (§ s) , unfinite (§ s))

----------------------------------------------------------------------
-- Atoms [Section 2.1]
----------------------------------------------------------------------
{- We could just take atoms to be given by natural numbers, but it
seems more elegant to use what is effectively a W-type that emphasises
one of the key properties of atoms (apart from having decidable
equality), namely that they are "unfinite" in the sense that for every
finite set of atoms there is an atom not in that set. -}

data 𝔸 : Set where
  new𝔸 : Fset 𝔸 → 𝔸

-- Equality of atoms is decidable
deceq𝔸 : (x y : 𝔸) → Dec (x ≡ y)
deceq𝔸s : (xs ys : Fset 𝔸) → Dec (xs ≡ ys)

deceq𝔸 (new𝔸 xs) (new𝔸 ys) with deceq𝔸s xs ys
... | neq f = neq λ{refl → f refl}
... | equ   = equ
deceq𝔸s Ø Ø = equ
deceq𝔸s [ x ] [ y ] with deceq𝔸 x y
... | neq f = neq λ{refl → f refl}
... | equ   = equ
deceq𝔸s (xs ∪ _ )  (ys ∪ _  ) with deceq𝔸s xs ys
deceq𝔸s (_  ∪ _ )  (_  ∪ _  ) | neq f = neq λ{ refl → f refl}
deceq𝔸s (_  ∪ xs') (_  ∪ ys') | equ with deceq𝔸s xs' ys'
deceq𝔸s (_  ∪ _ )  (_  ∪ _  ) | equ | neq g = neq λ p → g (∪inj₂ p)
deceq𝔸s (_  ∪ _ )  (_  ∪ _  ) | equ | equ = equ
deceq𝔸s Ø [ _ ] = neq λ()
deceq𝔸s Ø (_ ∪ _) = neq λ()
deceq𝔸s [ _ ] Ø = neq λ()
deceq𝔸s [ _ ] (_ ∪ _) = neq λ()
deceq𝔸s (_ ∪ _) Ø = neq λ()
deceq𝔸s (_ ∪ _) [ _ ] = neq λ()

instance
  hasDecEq𝔸 : hasDecEq 𝔸
  _≐_ {{hasDecEq𝔸}} = deceq𝔸
  hasDecEqFset𝔸 : hasDecEq (Fset 𝔸)
  _≐_ {{hasDecEqFset𝔸}} = deceq𝔸s

----------------------------------------------------------------------
-- The "unfinite" property of atoms [Equation (1)]
----------------------------------------------------------------------

-- A well-founded relation between atoms
data _≺_ : (a y : 𝔸) → Set where
  ≺new𝔸 :
    {a : 𝔸}
    {as : Fset 𝔸}
    (_ : a ∈ as)
    → ------------
    a ≺ new𝔸 as

≺iswf : wf.iswf _≺_
≺iswf (new𝔸 as) = wf.acc λ{a (≺new𝔸 p) → α a p}
  where
  α : ∀ a {as} → a ∈ as → wf.Acc _≺_ a
  α a ∈[]     = ≺iswf a
  α a (∈∪₁ p) = α a p
  α a (∈∪₂ p) = α a p

instance
  Unfinite𝔸 : Unfinite 𝔸
  deceq    {{Unfinite𝔸}}    = hasDecEq𝔸
  new      {{Unfinite𝔸}}    = new𝔸
  unfinite {{Unfinite𝔸}} as =
    ¬∈→∉ λ p → wf.irrefl _≺_ ≺iswf (new𝔸 as) (≺new𝔸 p)

----------------------------------------------------------------------
-- Cofinite quantifer ("for all but finitely many...") [Definition 2.1]
----------------------------------------------------------------------
infix 2 Cof
record Cof
  {l : Level}
  (A : Set l)
  {{α : hasDecEq A}}
  (P : A → Set l)
  : ----------------
  Set l
  where
  constructor Иi
  field
    Иe₁ : Fset A
    Иe₂ : (x : A){{_ : x ∉ Иe₁}} → P x

open Cof public

syntax Cof A (λ x → P) = И x ∶ A , P
