module Category where

open import Prelude
open import Unfinite
open import oc-Sets
open import Freshness
open import LocalClosedness
open import Support
open import AbstractionConcretion
open import RenamingRendexingSwapping

----------------------------------------------------------------------
-- Morphisms of oc-sets [Equation (40)]
----------------------------------------------------------------------
record oc-hom
  {X Y : Set}
  {{_ : oc X}}
  {{_ : oc Y}}
  (f : X → Y)
  : ----------
  Set
  where
  constructor mkoc-hom
  field
    oc-hom-open  : ∀{i a} x → f((i ~> a)x) ≡ (i ~> a)(f x)
    oc-hom-close : ∀{i a} x → f((i <~ a)x) ≡ (i <~ a)(f x)

open oc-hom{{...}} public

module _
  (X Y : Set)
  {{_ : oc X}}
  {{_ : oc Y}}
  (f : X → Y)
  {{_ :  oc-hom f}}
  where
  oc-hom-# : ∀ a x → a # x → a # f x -- Equation (41)
  oc-hom-# a x a#x =
    proof
      (0 <~ a)(f x)
    ≡[ symm (oc-hom-close x) ]
      f((0 <~ a)x)
    ≡[ ap f a#x ]
      f x
    qed

  oc-hom-≻ : ∀ i x → i ≻ x → i ≻ f x -- Equation (42)
  oc-hom-≻  i x i≻x j with (a , e) ← i≻x j = (a ,
    (proof
      (j ~> a) (f x)
    ≡[ symm (oc-hom-open x) ]
      f((j ~> a)x)
    ≡[ ap f e ]
      f x
    qed))

----------------------------------------------------------------------
-- Morphisms of locally nameless sets [Section 3.2]
----------------------------------------------------------------------
record lns-hom
  {X Y : Set}
  {{_ : lns X}}
  {{_ : lns Y}}
  (f : X → Y)
  : -----------
  Set
  where
  constructor mklns-hom
  field
    {{ochom}} : oc-hom f

open lns-hom{{...}} public

----------------------------------------------------------------------
-- Cartesian product of locally nameless sets [Lemma 3.3]
----------------------------------------------------------------------
oc× : {X Y : Set}{{_ : oc X}}{{_ : oc Y}} → oc (X × Y)
_~>_ {{oc×}} i  a (x , y) = ((i ~> a)x , (i ~> a)y)
_<~_ {{oc×}} i  a (x , y) = ((i <~ a)x , (i <~ a)y)
oc₁ {{oc×}} i a b (x , y)
  rewrite oc₁ i a b x | oc₁ i a b y = refl
oc₂ {{oc×}} i j a (x , y)
  rewrite oc₂ i j a x | oc₂ i j a y = refl
oc₃ {{oc×}} i a (x , y)
    rewrite oc₃ i a x | oc₃ i a y = refl
oc₄ {{oc×}} i a (x , y)
  rewrite oc₄ i a x | oc₄ i a y = refl
oc₅ {{oc×}} i j a b (x , y)
  rewrite oc₅ i j a b x {{it}}
  | oc₅ i j a b y {{it}} = refl
oc₆ {{oc×}} i j a b (x , y)
  rewrite oc₆ i j a b x {{it}}
  | oc₆ i j a b y {{it}} = refl
oc₇ {{oc×}} i j a b (x , y)
  rewrite oc₇ i j a b x {{it}} {{it}}
  | oc₇ i j a b y {{it}} {{it}} = refl
oc₈ {{oc×}} i j a b (x , y)
  rewrite oc₈ i j a b x
  | oc₈ i j a b y = refl
oc₉ {{oc×}}  i j a b (x , y)
  rewrite oc₉ i j a b x
  | oc₉ i j a b y = refl

lns× : {X Y : Set}{{_ : lns X}}{{_ : lns Y}} → lns (X × Y)
ocSet {{lns×}} = oc×
asupp {{lns×}} (x , y) with Иi as f ← asupp x | Иi bs g ← asupp y =
  Иi (as ∪ bs) h
  where
  h :
    (c : 𝔸)
    {{_ : c ∉ as ∪ bs}}
    → -------------------------------
    ((0 <~ c)x , (0 <~ c)y) ≡ (x , y)
  h c {{∉∪}} rewrite f c {{it}} | g c {{it}} = refl
isupp {{lns×}} (x , y) with (i , p) ← isupp x | (j , q) ← isupp y =
  (max i j , h)
  where
  h :
    (k : ℕ)
    {{_ : max i j ≤ k}}
    → -----------------------------------------
    ∑ c ∶ 𝔸 , ((k ~> c)x , (k ~> c)y) ≡ (x , y)
  h k {{r}}
    with (a , e) ← p k {{≤trans ≤max₁ r}}
    | (b , e') ← q k {{≤trans ≤max₂ r}} = (a , ee')
    where
    ee' : ((k ~> a)x , (k ~> a)y) ≡ (x , y)
    ee' rewrite e | ≻2 {a = b} {a} e' = refl

----------------------------------------------------------------------
-- Dependent product of locally nameless sets
----------------------------------------------------------------------
oc∑ :
  (X : Set)
  (Y : X → Set)
  {{ocY : ∀{x} → oc (Y x)}}
  → -----------------------
  oc (∑ X Y)
_~>_ {{oc∑ X Y}} i a (x , y) = (x , (i ~> a)y)
_<~_ {{oc∑ X Y}} i a (x , y) = (x , (i <~ a)y)
oc₁  {{oc∑ X Y}} i a b (_ , y)
  rewrite oc₁ i a b y = refl
oc₂  {{oc∑ X Y}} i j a (_ , y)
  rewrite oc₂ i j a y = refl
oc₃  {{oc∑ X Y}} i a (_ , y)
  rewrite oc₃ i a y = refl
oc₄  {{oc∑ X Y}} i a (_ , y)
  rewrite oc₄ i a y = refl
oc₅  {{oc∑ X Y}} i j a b (_ , y)
  rewrite oc₅ i j a b y {{it}} = refl
oc₆  {{oc∑ X Y}} i j a b (_ , y)
  rewrite oc₆ i j a b y {{it}} = refl
oc₇  {{oc∑ X Y}} i j a b (_ , y)
  rewrite oc₇ i j a b y {{it}} {{it}} = refl
oc₈  {{oc∑ X Y}}  i j a b (_ , y)
  rewrite oc₈ i j a b y = refl
oc₉  {{oc∑ X Y}} i j a b (_ , y)
  rewrite oc₉ i j a b y = refl

lns∑ :
  (X : Set)
  (Y : X → Set)
  {{lnsY : ∀{x} → lns (Y x)}}
  → -------------------------
  lns (∑ X Y)
ocSet {{lns∑ X Y {{lnsY}}}} = oc∑ X Y {{λ{x} → ocSet{{lnsY {x}}}}}
asupp {{lns∑ X Y {{lnsY}}}} (x , y) with Иi и₁ и₂ ← asupp y = Иi и₁ и₂'
  where
  instance
    _ : oc (Y x)
    _ = ocSet{{lnsY {x}}}
  и₂' :
    (a : 𝔸)
    {{_ : a ∉ и₁}}
    → ------------------------
    (x , (0 <~ a) y) ≡ (x , y)
  и₂' a = ap (x ,_) (и₂ a)
isupp {{lns∑ X Y {{lnsY}}}} (x , y) with (i , f) ← isupp y = (i , g)
  where
  instance
    _ : oc (Y x)
    _ = ocSet{{lnsY {x}}}
  g :
    (j : ℕ)
    {{_ : i ≤ j}}
    → ----------------------------------
    ∑ a ∶ 𝔸 , (x , (j ~> a) y) ≡ (x , y)
  g j with (a , p) ← f j = (a , ap (x ,_) p)
