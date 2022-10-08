module FullTransformationSemigroup where

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
module _ (S : Set){{_  : Unfinite S}} where
  --------------------------------------------------------------------
  -- Full transformation semigroup T_S [Definition 3.4 & Fig. 2]
  --------------------------------------------------------------------
  record TS (X : Set) : Set where
    -- Giving an element of TS S X amounts to giving an action of the
    -- full transformation monoid T_S on X
    field
      τ : S → S → X → X
      ε : S → S → X → X
      TS₁ :
        (a : S)
        (x : X)
        → ---------
        τ a a x ≡ x
      TS₂ :
        (a b : S)
        (x : X)
        → -----------------
        τ a b (τ a b x) ≡ x
      TS₃ :
        (a b c d : S)
        (x : X)
        {{_ : b ≠ c}}
        {{_ : c ≠ a}}
        {{_ : a ≠ d}}
        {{_ : d ≠ b}}
        → -------------------------------
        τ a b (τ c d x) ≡ τ c d (τ a b x)
      TS₄ :
        (a b c : S)
        (x : X)
        {{_ : b ≠ c}}
        {{_ : c ≠ a}}
        → -------------------------------
        τ a b (τ c a x) ≡ τ c b (τ a b x)
      TS₅ :
        (a : S)
        (x : X)
        → ---------
        ε a a x ≡ x
      TS₆ :
        (a b c : S)
        (x : X)
        {{_ : a ≠ c}}
        → -----------------------
        ε b a (ε c a x) ≡ ε c a x
      TS₇ :
        (a b c : S)
        (x : X)
        → -------------------------------
        ε c b (ε b a x) ≡ ε c a (ε c b x)
      TS₈ :
        (a b c d : S)
        (x : X)
        {{_ : b ≠ c}}
        {{_ : c ≠ a}}
        {{_ : a ≠ d}}
        → -------------------------------
        ε b a (ε d c x) ≡ ε d c (ε b a x)
      TS₉ :
        (a b c : S)
        (x : X)
        {{_ : b ≠ c}}
        → -------------------------------
        ε c b (τ a b x) ≡ ε a b (ε c a x)
      TS₁₀ :
        (a b c d : S)
        (x : X)
        {{_ : b ≠ c}}
        {{_ : c ≠ a}}
        {{_ : a ≠ d}}
        {{_ : d ≠ b}}
        → -------------------------------
        τ a b (ε d c x) ≡ ε d c (τ a b x)
      TS₁₁ :
        (a b c : S)
        (x : X)
        {{_ : b ≠ c}}
        {{_ : c ≠ a}}
        → -------------------------------
        τ a b (ε a c x) ≡ ε b c (τ a b x)
      TS₁₂ :
        (a b c : S)
        (x : X)
        {{_ : b ≠ c}}
        {{_ : c ≠ a}}
        → -------------------------------
        τ a b (ε c a x) ≡ ε c b (τ a b x)
      TS₁₃ :
        (a b : S)
        (x : X)
        → -------------------------------
        τ a b (ε b a x) ≡ ε a b (τ a b x)

  open TS{{...}} public

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
        {{_ : c ≠ a}}
        {{_ : a ≠ d}}
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
    и₂ d {{∉[]}} with a ≐ c
    ... | equ = RN₂ _ _ _ _
    ... | neq g =
      let
        instance
          _ : a ≠ c
          _ = ¬≡→≠ g
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

  --------------------------------------------------------------------
  -- Name swapping operation
  --------------------------------------------------------------------
  module _ {X : Set}{{_ : fsRenset X}} where
    σ : S → S → X → X
    σ a b x  =
      let c = new ([ a ] ∪ [ b ] ∪ Иe₁ (rsupp x)) in
      ρ b c (ρ a b (ρ c a x))

    σwelldef :
      (a b c d : S)
      (x : X)
      {{_ : c ♯ x}}
      {{_ : c ≠ a}}
      {{_ : c ≠ b}}
      {{_ : d ♯ x}}
      {{_ : d ≠ a}}
      {{_ : d ≠ b}}
      → -----------------------
      ρ b c (ρ a b (ρ c a x)) ≡
      ρ b d (ρ a b (ρ d a x))
    σwelldef a b c d x with d ≐ c
    ... | equ = refl
    ... | neq f =
      let
        instance
          _ : d ≠ c
          _ = ¬≡→≠  f
          _ : b ≠ c
          _ = symm≠ c b it
      in
      proof
        ρ b c (ρ a b (ρ c a x))
      ≡[ ap (ρ b c) (symm (♯≡ _ d b {{♯ρ _ b a d {{♯ρ x a c d}}}})) ]
        ρ b c (ρ b d (ρ a b (ρ c a x)))
      ≡[ symm (RN₃ _ _ _ _) ]
        ρ b d (ρ d c (ρ a b (ρ c a x)))
      ≡[ ap (ρ b d) (RN₄ _ _ _ _ _) ]
        ρ b d (ρ a b (ρ d c (ρ c a x)))
      ≡[ ap (ρ b d ∘ ρ a b) (RN₃ _ _ _ _) ]
        ρ b d (ρ a b (ρ d a (ρ d c x)))
      ≡[ ap (ρ b d ∘ ρ a b ∘ ρ d a) (♯≡ x c d) ]
        ρ b d (ρ a b (ρ d a x))
      qed

    σfresh :
      (a b c : S)
      (x : X)
      {{_ : c ♯ x}}
      {{_ : c ≠ a}}
      {{_ : c ≠ b}}
      → -------------------------------
      σ a b x ≡ ρ b c (ρ a b (ρ c a x))
    σfresh a b c x =
      let
        as = [ a ] ∪ [ b ] ∪ Иe₁ (rsupp x)
        d = new as
        instance
          _ : d ♯ x
          _ = Иe₂ (rsupp x) d {{∉∪₂ (∉∪₂ (unfinite as))}}
          _ : d ≠ a
          _ = ∉[]₁ (∉∪₁ (unfinite as))
          _ : d ≠ b
          _ = ∉[]₁ (∉∪₁ (∉∪₂ (unfinite as)))
      in σwelldef a b d c x

    ♯σ :
      (a b c : S)
      (x : X)
      {{_ : c ♯ x}}
      {{_ : c ≠ a}}
      {{_ : c ≠ b}}
      → -----------
      c ♯ σ a b x
    ♯σ a b c x rewrite σfresh a b c x {{it}}{{it}}{{it}} = ♯ρ' _ _ _

  --------------------------------------------------------------------
  -- Every finitely supported renset has an action of the full
  -- transformation semigroup T_S
  --------------------------------------------------------------------
  fsRenset→TS :
    {X : Set}
    {{_ : fsRenset X}}
    → ----------------
    TS X
  fsRenset→TS {X} = record
    { τ    = σ
    ; ε    = ρ
    ; TS₁  = f₁
    ; TS₂  = f₂
    ; TS₃  = f₃
    ; TS₄  = f₄
    ; TS₅  = RN₁
    ; TS₆  = RN₂
    ; TS₇  = RN₃
    ; TS₈  = RN₄
    ; TS₉  = f₉
    ; TS₁₀ = f₁₀
    ; TS₁₁ = f₁₁
    ; TS₁₂ = f₁₂
    ; TS₁₃ = f₁₃
    }
    where
    f₁ :
      (a : S)
      (x : X)
      → ---------
      σ a a x ≡ x
    f₁ a x =
      let
        as = [ a ] ∪ Иe₁ (rsupp x)
        c = new as
        instance
          c♯x : c ♯ x
          c♯x = Иe₂ (rsupp x) c {{∉∪₂ (unfinite as)}}
          _ : c ≠ a
          _ = ∉[]₁ (∉∪₁ (unfinite as))
      in
      proof
        σ a a x
      ≡[ σfresh a a c x ]
        ρ a c (ρ a a (ρ c a x))
      ≡[ ap (ρ a c) (RN₁ _ _) ]
        ρ a c (ρ c a x)
      ≡[ RN₃ _ _ _ _ ]
        ρ a a (ρ a c x)
      ≡[ RN₁ _ _ ]
        ρ a c x
      ≡[ ♯≡ x c a ]
        x
      qed
    f₂ :
      (a b : S)
      (x : X)
      → -----------------
      σ a b (σ a b x) ≡ x
    f₂ a b x with a ≐ b
    ... | equ =
      proof
        σ a a (σ a a x)
      ≡[ f₁ _ _ ]
        σ a a x
      ≡[ f₁ _ _ ]
        x
      qed
    ... | neq f =
      let
        as = [ a ] ∪ [ b ] ∪ Иe₁ (rsupp x)
        c = new as
        as' = [ c ] ∪ as
        c' = new as'
        instance
          _ : c' ♯ x
          _ = Иe₂ (rsupp x) c' {{∉∪₂ (∉∪₂ (∉∪₂ (unfinite as')))}}
          _ : c' ≠ a
          _ = ∉[]₁ (∉∪₁ (∉∪₂ (unfinite as')))
          _ : c' ≠ b
          _ = ∉[]₁ (∉∪₁ (∉∪₂ (∉∪₂ (unfinite as'))))
          _ : c' ♯ σ a b x
          _ = ♯σ a b c' x
          _ : c' ≠ c
          _ = ∉[]₁ (∉∪₁(unfinite as'))
          _ : c ≠ a
          _ = ∉[]₁ (∉∪₁ (unfinite as))
          _ : a ≠ c
          _ = symm≠ c a it
          _ : a ≠ b
          _ = ¬≡→≠  f
          _ : b ≠ a
          _ = symm≠ a b it
          _ : c ≠ b
          _ = ∉[]₁ (∉∪₁ (∉∪₂ (unfinite as)))
          _ : b ≠ c
          _ = symm≠ c b it
          _ : c ♯ x
          _ = Иe₂ (rsupp x) c {{∉∪₂ (∉∪₂ (unfinite as))}}
          _ : a ≠ c'
          _ = symm≠ c' a it
          _ : b ≠ c'
          _ = symm≠ c' b it
          _ : c ≠ c'
          _ = symm≠ c' c it
      in
      proof
        σ a b (σ a b x)
      ≡[ σfresh a b c' (σ a b x) ]
        ρ b c' (ρ a b (ρ c' a (σ a b x)))
      ≡[]
        ρ b c' (ρ a b (ρ c' a (ρ b c (ρ a b (ρ c a x)))))
      ≡[ ap (ρ b c' ∘ ρ a b) (RN₄ _ _ _ _ _) ]
        ρ b c' (ρ a b (ρ b c (ρ c' a (ρ a b (ρ c a x)))))
      ≡[ ap (ρ b c' ∘ ρ a b ∘ ρ b c) (RN₃ _ _ _ _) ]
        ρ b c' (ρ a b (ρ b c (ρ c' b (ρ c' a (ρ c a x)))))
      ≡[ ap (ρ b c' ∘ ρ a b ∘ ρ b c ∘ ρ c' b) (RN₂ _ _ _ _) ]
        ρ b c' (ρ a b (ρ b c (ρ c' b (ρ c a x))))
      ≡[ ap (ρ b c') (RN₃ _ _ _ _) ]
        ρ b c' (ρ a c (ρ a b (ρ c' b (ρ c a x))))
      ≡[ ap (ρ b c' ∘ ρ a c) (RN₂ _ _ _ _) ]
        ρ b c' (ρ a c (ρ c' b (ρ c a x)))
      ≡[ RN₄ _ _ _ _ _ ]
        ρ a c (ρ b c' (ρ c' b (ρ c a x)))
      ≡[ ap (ρ a c) (RN₃ _ _ _ _) ]
        ρ a c (ρ b b (ρ b c' (ρ c a x)))
      ≡[ ap (ρ a c) (RN₁ _ _) ]
        ρ a c (ρ b c' (ρ c a x))
      ≡[ RN₄ _ _ _ _ _ ]
        ρ b c' (ρ a c (ρ c a x))
      ≡[ ap (ρ b c') (RN₃ _ _ _ _) ]
        ρ b c' (ρ a a (ρ a c x))
      ≡[ ap (ρ b c') (RN₁ _ _) ]
        ρ b c' (ρ a c x)
      ≡[ ap (ρ b c') (♯≡ x c a) ]
        ρ b c' x
      ≡[ ♯≡ x c' b ]
        x
      qed

    f₃ :
      (a b c d : S)
      (x : X)
      {{_ : b ≠ c}}
      {{_ : c ≠ a}}
      {{_ : a ≠ d}}
      {{_ : d ≠ b}}
      → -------------------------------
      σ a b (σ c d x) ≡ σ c d (σ a b x)
    f₃ a b c d x =
      let
        as = [ a ] ∪ [ b ] ∪ [ c ] ∪ [ d ] ∪ Иe₁ (rsupp x)
        e = new as
        as' = [ e ] ∪ as
        e' = new as'
        instance
          _ : e ♯ x
          _ = Иe₂ (rsupp x) e {{∉∪₂ (∉∪₂ (∉∪₂ (∉∪₂ (unfinite as))))}}
          _ : e ≠ a
          _ = ∉[]₁ (∉∪₁ (unfinite as))
          _ : e ≠ b
          _ = ∉[]₁ (∉∪₁ (∉∪₂ (unfinite as)))
          _ : e ≠ c
          _ = ∉[]₁ (∉∪₁ (∉∪₂ (∉∪₂ (unfinite as))))
          _ : e ≠ d
          _ = ∉[]₁ (∉∪₁ (∉∪₂ (∉∪₂ (∉∪₂ (unfinite as)))))
          _ : e ♯ σ c d x
          _ = ♯σ c d e x
          _ : e' ♯ x
          _ = Иe₂ (rsupp x) e' {{∉∪₂ (∉∪₂ (∉∪₂ (∉∪₂ (∉∪₂ (unfinite as')))))}}
          _ : e' ≠ a
          _ = ∉[]₁ (∉∪₁ (∉∪₂ (unfinite as')))
          _ : e' ≠ b
          _ = ∉[]₁ (∉∪₁ (∉∪₂ (∉∪₂ (unfinite as'))))
          _ : e' ≠ c
          _ = ∉[]₁ (∉∪₁ (∉∪₂ (∉∪₂ (∉∪₂ (unfinite as')))))
          _ : e' ≠ d
          _ = ∉[]₁ (∉∪₁ (∉∪₂ (∉∪₂ (∉∪₂ (∉∪₂ (unfinite as'))))))
          _ : e' ♯ σ a b x
          _ = ♯σ a b e' x
          _ : e ≠ e'
          _ = symm≠ e' e (∉[]₁ (∉∪₁ (unfinite as')))
          _ : a ≠ e'
          _ = symm≠ e' a it
          _ : d ≠ a
          _ = symm≠ a d it
          _ : b ≠ e'
          _ = symm≠ e' b it
          _ : d ≠ e
          _ = symm≠ e d it
          _ : b ≠ d
          _ = symm≠ d b it
          _ : c ≠ b
          _ = symm≠ b c it
          _ : c ≠ e
          _ = symm≠ e c it
          _ : a ≠ c
          _ = symm≠ c a it
          _ : e' ≠ e
          _ = symm≠ e e' it
      in
      proof
        σ a b (σ c d x)
      ≡[ σfresh a b e (σ c d x) ]
        ρ b e (ρ a b (ρ e a (σ c d x)))
      ≡[ ap (ρ b e ∘ ρ a b ∘ ρ e a) (σfresh c d e' x) ]
        ρ b e (ρ a b (ρ e a (ρ d e' (ρ c d (ρ e' c x)))))
      ≡[ ap (ρ b e ∘ ρ a b) (RN₄ _ _ _ _ _) ]
        ρ b e (ρ a b (ρ d e' (ρ e a (ρ c d (ρ e' c x)))))
      ≡[ ap (ρ b e) (RN₄ _ _ _ _ _) ]
        ρ b e (ρ d e' (ρ a b (ρ e a (ρ c d (ρ e' c x)))))
      ≡[ RN₄ _ _ _ _ _ ]
        ρ d e' (ρ b e (ρ a b (ρ e a (ρ c d (ρ e' c x)))))
      ≡[ ap (ρ d e' ∘ ρ b e ∘ ρ a b) (RN₄ _ _ _ _ _) ]
        ρ d e' (ρ b e (ρ a b (ρ c d (ρ e a (ρ e' c x)))))
      ≡[ ap (ρ d e' ∘ ρ b e) (RN₄ _ _ _ _ _) ]
        ρ d e' (ρ b e (ρ c d (ρ a b (ρ e a (ρ e' c x)))))
      ≡[ ap (ρ d e') (RN₄ _ _ _ _ _) ]
        ρ d e' (ρ c d (ρ b e (ρ a b (ρ e a (ρ e' c x)))))
      ≡[ ap (ρ d e' ∘ ρ c d ∘ ρ b e ∘ ρ a b) (RN₄ _ _ _ _ _) ]
        ρ d e' (ρ c d (ρ b e (ρ a b (ρ e' c (ρ e a x)))))
      ≡[ ap (ρ d e' ∘ ρ c d ∘ ρ b e) (RN₄ _ _ _ _ _) ]
        ρ d e' (ρ c d (ρ b e (ρ e' c (ρ a b (ρ e a x)))))
      ≡[ ap (ρ d e' ∘ ρ c d) (RN₄ _ _ _ _ _) ]
        ρ d e' (ρ c d (ρ e' c (ρ b e (ρ a b (ρ e a x)))))
      ≡[ ap (ρ d e' ∘ ρ c d ∘ ρ e' c) (symm (σfresh a b e x)) ]
        ρ d e' (ρ c d (ρ e' c (σ a b x)))
      ≡[ symm (σfresh c d e' (σ a b x)) ]
        σ c d (σ a b x)
      qed

    f₄ :
      (a b c : S)
      (x : X)
      {{_ : b ≠ c}}
      {{_ : c ≠ a}}
      → -------------------------------
      σ a b (σ c a x) ≡ σ c b (σ a b x)
    f₄ a b c x with b ≐ a
    ... | equ =
      proof
        σ a a (σ c a x)
      ≡[ f₁ _ _ ]
        σ c a x
      ≡[ ap (σ c a) (symm (f₁ _ _)) ]
        σ c a (σ a a x)
      qed
    ... | neq f =
      let
        as = [ a ] ∪ [ b ] ∪ [ c ] ∪ Иe₁ (rsupp x)
        e = new as
        as' = [ e ] ∪ as
        e' = new as'
        instance
          _ : e ♯ x
          _ = Иe₂ (rsupp x) e {{∉∪₂ (∉∪₂ (∉∪₂ (unfinite as)))}}
          _ : e ≠ a
          _ = ∉[]₁ (∉∪₁ (unfinite as))
          _ : e ≠ b
          _ = ∉[]₁ (∉∪₁ (∉∪₂ (unfinite as)))
          _ : e ≠ c
          _ = ∉[]₁ (∉∪₁ (∉∪₂ (∉∪₂ (unfinite as))))
          _ : e ♯ σ c a x
          _ = ♯σ c a e x
          _ : e' ♯ x
          _ = Иe₂ (rsupp x) e' {{∉∪₂ (∉∪₂ (∉∪₂ (∉∪₂ (unfinite as'))))}}
          _ : e' ≠ c
          _ = ∉[]₁ (∉∪₁ (∉∪₂ (∉∪₂ (∉∪₂ (unfinite as')))))
          _ : e' ≠ a
          _ = ∉[]₁ (∉∪₁ (∉∪₂ (unfinite as')))
          _ : e' ♯ x
          _ = Иe₂ (rsupp x) e' {{∉∪₂ (∉∪₂ (∉∪₂ (∉∪₂ (unfinite as'))))}}
          _ : e' ≠ a
          _ = ∉[]₁ (∉∪₁ (∉∪₂ (unfinite as')))
          _ : e' ≠ b
          _ = ∉[]₁ (∉∪₁ (∉∪₂ (∉∪₂ (unfinite as'))))
          _ : e ♯ σ a b x
          _ = ♯σ a b e x
          _ : a ≠ e'
          _ = symm≠ e' a it
          _ : b ≠ e'
          _ = symm≠ e' b it
          _ : a ≠ c
          _ = symm≠ c a it
          _ : e' ≠ e
          _ = ∉[]₁ (∉∪₁ (unfinite as'))
          _ : e ≠ e'
          _ = symm≠ e' e it
          _ : c ≠ e'
          _ = symm≠ e' c it
          _ : c ≠ b
          _ = symm≠ b c it
          _ : b ≠ a
          _ = ¬≡→≠  f
      in
      proof
        σ a b (σ c a x)
      ≡[ σfresh a b e (σ c a x) ]
        ρ b e (ρ a b (ρ e a (σ c a x)))
      ≡[ ap (ρ b e ∘ ρ a b ∘ ρ e a) (σfresh c a e' x) ]
        ρ b e (ρ a b (ρ e a (ρ a e' (ρ c a (ρ e' c x)))))
      ≡[ ap (ρ b e ∘ ρ a b) (RN₃ _ _ _ _) ]
        ρ b e (ρ a b (ρ e e' (ρ e a (ρ c a (ρ e' c x)))))
      ≡[ ap (ρ b e ∘ ρ a b ∘ ρ e e') (RN₂ _ _ _ _) ]
        ρ b e (ρ a b (ρ e e' (ρ c a (ρ e' c x))))
      ≡[ ap (ρ b e ∘ ρ a b) (RN₄ _ _ _ _ _) ]
        ρ b e (ρ a b (ρ c a (ρ e e' (ρ e' c x))))
      ≡[ ap (ρ b e ∘ ρ a b ∘ ρ c a) (RN₃ _ _ _ _) ]
        ρ b e (ρ a b (ρ c a (ρ e c (ρ e e' x))))
      ≡[ ap (ρ b e ∘ ρ a b ∘ ρ c a ∘ ρ e c) (♯≡ x e' e) ]
        ρ b e (ρ a b (ρ c a (ρ e c x)))
      ≡[ ap (ρ b e ∘ ρ a b ∘ ρ c a)
         (symm (♯≡ (ρ e c x) e' c {{♯ρ x c e e'}})) ]
        ρ b e (ρ a b (ρ c a (ρ c e' (ρ e c x))))
      ≡[ ap (ρ b e ∘ ρ a b) (symm (RN₃ _ _ _ _)) ]
        ρ b e (ρ a b (ρ c e' (ρ e' a (ρ e c x))))
      ≡[ ap (ρ b e) (symm (RN₄ _ _ _ _ _)) ]
        ρ b e (ρ c e' (ρ a b (ρ e' a (ρ e c x))))
      ≡[ ap (ρ b e ∘ ρ c e') (symm (RN₂ _ _ _ _)) ]
        ρ b e (ρ c e' (ρ c b (ρ a b (ρ e' a (ρ e c x)))))
      ≡[ ap (ρ b e ∘ ρ c e' ∘ ρ c b ∘ ρ a b) (symm (RN₄ _ _ _ _ _)) ]
        ρ b e (ρ c e' (ρ c b (ρ a b (ρ e c (ρ e' a x)))))
      ≡[ ap (ρ b e ∘ ρ c e' ∘ ρ c b) (symm (RN₄ _ _ _ _ _)) ]
        ρ b e (ρ c e' (ρ c b (ρ e c (ρ a b (ρ e' a x)))))
      ≡[ ap (ρ b e) (symm (RN₃ _ _ _ _)) ]
        ρ b e (ρ c b (ρ b e' (ρ e c (ρ a b (ρ e' a x)))))
      ≡[ ap (ρ b e ∘ ρ c b) (symm (RN₄ _ _ _ _ _)) ]
        ρ b e (ρ c b (ρ e c (ρ b e' (ρ a b (ρ e' a x)))))
      ≡[ ap (ρ b e ∘ ρ c b ∘ ρ e c) (symm (σfresh a b e' x)) ]
        ρ b e (ρ c b (ρ e c (σ a b x)))
      ≡[ symm (σfresh c b e (σ a b x)) ]
        σ c b (σ a b x)
      qed

    f₉ :
      (a b c : S)
      (x : X)
      {{_ : b ≠ c}}
      → -------------------------------
      ρ c b (σ a b x) ≡ ρ a b (ρ c a x)
    f₉ a b c x with b ≐ a
    ... | equ =
      proof
        ρ c a (σ a a x)
      ≡[ ap (ρ c a) (f₁ _ _) ]
        ρ c a x
      ≡[ symm (RN₁ _ _)  ]
        ρ a a (ρ c a x)
      qed
    ... | neq f =
      let
        as = [ a ] ∪ [ b ] ∪ [ c ] ∪ Иe₁ (rsupp x)
        d = new as
        instance
          _ : d ♯ x
          _ = Иe₂ (rsupp x) d {{∉∪₂ (∉∪₂ (∉∪₂ (unfinite as)))}}
          _ : d ≠ a
          _ = ∉[]₁ (∉∪₁ (unfinite as))
          _ : d ≠ b
          _ = ∉[]₁ (∉∪₁ (∉∪₂ (unfinite as)))
          _ : b ≠ a
          _ = ¬≡→≠  f
          _ : c ≠ b
          _ = symm≠ b c it
          _ : a ≠ d
          _ = symm≠ d a it
          _ : b ≠ d
          _ = symm≠ d b it
      in
      proof
        ρ c b (σ a b x)
      ≡[ ap (ρ c b) (σfresh a b d x) ]
        ρ c b (ρ b d (ρ a b (ρ d a x)))
      ≡[ RN₃ _ _ _ _ ]
        ρ c d (ρ c b (ρ a b (ρ d a x)))
      ≡[ ap (ρ c d) (RN₂ _ _ _ _) ]
        ρ c d (ρ a b (ρ d a x))
      ≡[ RN₄ _ _ _ _ _ ]
        ρ a b (ρ c d (ρ d a x))
      ≡[ ap (ρ a b) (RN₃ _ _ _ _) ]
        ρ a b (ρ c a (ρ c d x))
      ≡[ ap (ρ a b ∘ ρ c a) (♯≡ x d c) ]
        ρ a b (ρ c a x)
      qed

    f₁₀ :
      (a b c d : S)
      (x : X)
      {{_ : b ≠ c}}
      {{_ : c ≠ a}}
      {{_ : a ≠ d}}
      {{_ : d ≠ b}}
      → -------------------------------
      σ a b (ρ d c x) ≡ ρ d c (σ a b x)
    f₁₀ a b c d x =
      let
        as = [ a ] ∪ [ b ] ∪ [ c ] ∪ [ d ] ∪ Иe₁ (rsupp x)
        e = new as
        instance
          _ : e ♯ x
          _ = Иe₂ (rsupp x) e {{∉∪₂ (∉∪₂ (∉∪₂ (∉∪₂ (unfinite as))))}}
          _ : e ≠ a
          _ = ∉[]₁ (∉∪₁ (unfinite as))
          _ : e ≠ b
          _ = ∉[]₁ (∉∪₁ (∉∪₂ (unfinite as)))
          _ : e ≠ c
          _ =  ∉[]₁ (∉∪₁ (∉∪₂ (∉∪₂ (unfinite as))))
          _ : e ≠ d
          _ = ∉[]₁ (∉∪₁ (∉∪₂ (∉∪₂ (∉∪₂ (unfinite as)))))
          _ : e ♯ ρ d c x
          _ = ♯ρ x c d e
          _ : a ≠ c
          _ = symm≠ c a it
          _ : d ≠ a
          _ = symm≠ a d it
          _ : d ≠ e
          _ = symm≠ e d it
          _ : c ≠ b
          _ = symm≠ b c it
          _ : b ≠ d
          _ = symm≠ d b it
          _ : c ≠ e
          _ = symm≠ e c it
      in
      proof
        σ a b (ρ d c x)
      ≡[ σfresh a b e (ρ d c x) ]
        ρ b e (ρ a b (ρ e a (ρ d c x)))
      ≡[ ap (ρ b e ∘ ρ a b) (RN₄ _ _ _ _ _) ]
        ρ b e (ρ a b (ρ d c (ρ e a x)))
      ≡[ ap (ρ b e) (RN₄ _ _ _ _ _) ]
        ρ b e (ρ d c (ρ a b (ρ e a x)))
      ≡[ RN₄ _ _ _ _ _ ]
        ρ d c (ρ b e (ρ a b (ρ e a x)))
      ≡[ ap (ρ d c) (symm (σfresh a b e x)) ]
        ρ d c (σ a b x)
      qed

    f₁₁ :
      (a b c : S)
      (x : X)
      {{_ : b ≠ c}}
      {{_ : c ≠ a}}
      → -------------------------------
      σ a b (ρ a c x) ≡ ρ b c (σ a b x)
    f₁₁ a b c x =
      let
        as = [ a ] ∪ [ b ] ∪ [ c ] ∪ Иe₁ (rsupp x)
        d = new as
        instance
          _ : d ♯ x
          _ = Иe₂ (rsupp x) d {{∉∪₂ (∉∪₂ (∉∪₂ (unfinite as)))}}
          _ : d ≠ a
          _ = ∉[]₁ (∉∪₁ (unfinite as))
          _ : d ≠ b
          _ = ∉[]₁ (∉∪₁ (∉∪₂ (unfinite as)))
          _ : d ≠ c
          _ =  ∉[]₁ (∉∪₁ (∉∪₂ (∉∪₂ (unfinite as))))
          _ : d ♯ ρ a c x
          _ = ♯ρ x c a d
          _ :  a ≠ c
          _ = symm≠ c a it
          _ : c ≠ b
          _ = symm≠ b c it
          _ : b ≠ d
          _ = symm≠ d b it
      in
      proof
        σ a b (ρ a c x)
      ≡[ σfresh a b d (ρ a c x) ]
        ρ b d (ρ a b (ρ d a (ρ a c x)))
      ≡[ ap (ρ b d ∘ ρ a b) (RN₃ _ _ _ _) ]
        ρ b d (ρ a b (ρ d c (ρ d a x)))
      ≡[ ap (ρ b d) (RN₄ _ _ _ _ _) ]
        ρ b d (ρ d c (ρ a b (ρ d a x)))
      ≡[ RN₃ _ _ _ _ ]
        ρ b c (ρ b d (ρ a b (ρ d a x)))
      ≡[ ap (ρ b c) (symm (σfresh a b d x)) ]
        ρ b c (σ a b x)
      qed

    f₁₂ :
      (a b c : S)
      (x : X)
      {{_ : b ≠ c}}
      {{_ : c ≠ a}}
      → -------------------------------
      σ a b (ρ c a x) ≡ ρ c b (σ a b x)
    f₁₂ a b c x with b ≐ a
    ... | equ =
      proof
        σ a a (ρ c a x)
      ≡[ f₁ _ _ ]
        ρ c a x
      ≡[ ap (ρ c a) (symm (f₁ _ _)) ]
        ρ c a (σ a a x)
      qed
    ... | neq f =
      let
        as = [ a ] ∪ [ b ] ∪ [ c ] ∪ Иe₁ (rsupp x)
        d = new as
        instance
          _ : d ♯ x
          _ = Иe₂ (rsupp x) d {{∉∪₂ (∉∪₂ (∉∪₂ (unfinite as)))}}
          _ : d ≠ a
          _ = ∉[]₁ (∉∪₁ (unfinite as))
          _ : d ≠ b
          _ = ∉[]₁ (∉∪₁ (∉∪₂ (unfinite as)))
          _ : d ≠ c
          _ =  ∉[]₁ (∉∪₁ (∉∪₂ (∉∪₂ (unfinite as))))
          _ : d ♯ ρ c a x
          _ = ♯ρ x a c d
          _ :  a ≠ c
          _ = symm≠ c a it
          _ : d ♯ ρ a b (ρ c a x)
          _ = ♯ρ _ b a d
          _ : b ≠ a
          _ = ¬≡→≠  f
          _ : c ≠ b
          _ = symm≠ b c it
          _ : a ≠ d
          _ = symm≠ d a it
          _ : b ≠ d
          _ = symm≠ d b it
      in
      proof
        σ a b (ρ c a x)
      ≡[ σfresh a b d (ρ c a x) ]
        ρ b d (ρ a b (ρ d a (ρ c a x)))
      ≡[ ap (ρ b d ∘ ρ a b) (RN₂ _ _ _ _) ]
        ρ b d (ρ a b (ρ c a x))
      ≡[ ♯≡ _ d b ]
        ρ a b (ρ c a x)
      ≡[ ap (ρ a b ∘ ρ c a) (symm (♯≡ x d c)) ]
        ρ a b (ρ c a (ρ c d x))
      ≡[ ap (ρ a b) (symm (RN₃ _ _ _ _)) ]
        ρ a b (ρ c d (ρ d a x))
      ≡[ symm (RN₄ _ _ _ _ _) ]
        ρ c d (ρ a b (ρ d a x))
      ≡[ ap (ρ c d) (symm (RN₂ _ _ _ _)) ]
        ρ c d (ρ c b (ρ a b (ρ d a x)))
      ≡[ symm (RN₃ _ _ _ _) ]
        ρ c b (ρ b d (ρ a b (ρ d a x)))
      ≡[ ap (ρ c b) (symm (σfresh a b d x)) ]
        ρ c b (σ a b x)
      qed

    f₁₃ :
      (a b : S)
      (x : X)
      → -------------------------------
      σ a b (ρ b a x) ≡ ρ a b (σ a b x)
    f₁₃ a b x  with  b ≐ a
    ... | equ =
      proof
        σ a a (ρ a a x)
      ≡[ f₁ _ _ ]
        ρ a a x
      ≡[ ap (ρ a a) (symm (f₁ _ _)) ]
        ρ a a (σ a a x)
      qed
    ... | neq f =
      let
        as = [ a ] ∪ [ b ] ∪ Иe₁ (rsupp x)
        c = new as
        instance
          _ : c ♯ x
          _ = Иe₂ (rsupp x) c {{∉∪₂ (∉∪₂ (unfinite as))}}
          _ : c ≠ a
          _ = ∉[]₁ (∉∪₁ (unfinite as))
          _ : c ≠ b
          _ = ∉[]₁ (∉∪₁ (∉∪₂ (unfinite as)))
          _ : c ♯ ρ b a x
          _ = ♯ρ x a b c
          _ : b ≠ a
          _ = ¬≡→≠  f
          _ : a ≠ b
          _ = symm≠ b a it
          _ : c ♯ ρ a b x
          _ = ♯ρ x b a c
          _ : a ≠ c
          _ = symm≠ c a it
          _ : b ≠ c
          _ = symm≠ c b it
      in
      proof
        σ a b (ρ b a x)
      ≡[ σfresh a b c (ρ b a x) ]
        ρ b c (ρ a b (ρ c a (ρ b a x)))
      ≡[ ap (ρ b c ∘ ρ a b) (RN₂ _ _ _ _) ]
        ρ b c (ρ a b (ρ b a x))
      ≡[ ap (ρ b c) (RN₃ _ _ _ _) ]
        ρ b c (ρ a a (ρ a b x))
      ≡[ ap (ρ b c) (RN₁ _ _) ]
        ρ b c (ρ a b x)
      ≡[ ♯≡ _ c b ]
        ρ a b x
      ≡[ ap (ρ a b) (symm (♯≡ x c a)) ]
        ρ a b (ρ a c x)
      ≡[ ap (ρ a b) (symm (RN₁ _ _)) ]
        ρ a b (ρ a a (ρ a c x))
      ≡[ ap (ρ a b) (symm (RN₃ _ _ _ _)) ]
        ρ a b (ρ a c (ρ c a x))
      ≡[ symm (RN₄ _ _ _ _ _) ]
        ρ a c (ρ a b (ρ c a x))
      ≡[ ap (ρ a c) (symm (RN₂ _ _ _ _)) ]
        ρ a c (ρ a b (ρ a b (ρ c a x)))
      ≡[ symm (RN₃ _ _ _ _) ]
        ρ a b (ρ b c (ρ a b (ρ c a x)))
      ≡[ ap (ρ a b) (symm (σfresh a b c x)) ]
        ρ a b (σ a b x)
      qed

{- Composing fsRenset→TS with lns→fsRenset, we get a proof of the
 existence part of Proposition 3.8 from Proposition 3.7 (which is not
 formalized here). -}
