module RenamingRendexingSwapping where

open import Prelude
open import Unfinite
open import oc-Sets
open import Freshness
open import LocalClosedness
open import Support
open import AbstractionConcretion

----------------------------------------------------------------------
-- Lemma 2.16
----------------------------------------------------------------------
module _
  {X : Set}
  {{_ : lns X}}
  {a b : 𝔸}
  {i j : ℕ}
  {x : X}
  where
  ~><~ : -- Equation (19)
    (p : i ≻ x)
    (q : j ≻ x)
    → ---------------------------------------
    (i ~> b)((i <~ a)x) ≡ (j ~> b)((j <~ a)x)
  ~><~ p q  =
    proof
      (i ~> b)((i <~ a)x)
    ≡[ ap ((i ~> b) ∘ (i <~ a)) (symm (≻3 q ≤refl)) ]
      (i ~> b)((i <~ a)((j ~> b)x))
    ≡[ oc₈ _ _ _ _ _ ]
      (j ~> b)((j <~ a)((i ~> a)x))
    ≡[ ap ((j ~> b) ∘ (j <~ a)) (≻3 p ≤refl) ]
      (j ~> b)((j <~ a)x)
    qed

  <~~> : -- Equation (20)
    (p : a # x)
    (q : b # x)
    → ---------------------------------------
    (j <~ a)((i ~> a)x) ≡ (j <~ b)((i ~> b)x)
  <~~> p q =
    proof
      (j <~ a)((i ~> a)x)
    ≡[ ap ((j <~ a) ∘ (i ~> a)) (symm (#2 q)) ]
      (j <~ a)((i ~> a)((j <~ b)x))
    ≡[ oc₉ _ _ _ _ _ ]
      (j <~ b)((i ~> b)((i <~ a)x))
    ≡[ ap ((j <~ b) ∘ (i ~> b)) (#2 p) ]
      (j <~ b)((i ~> b)x)
    qed

----------------------------------------------------------------------
-- Renaming
----------------------------------------------------------------------
infix 5 _↤_
_↤_ : {X : Set}{{_ : lns X}} → 𝔸 → 𝔸 → X → X
(b ↤ a)x =
  let i = π₁ (isupp x) in
  (i ~> b)((i <~ a)x) -- Equation(21)

↤fresh :
  {X : Set}
  {{_ : lns X}}
  {a b : 𝔸}
  (x : X)
  (i : ℕ)
  (_ : i ≻ x)
  → ----------------------------
  (b ↤ a)x ≡ (i ~> b)((i <~ a)x)
↤fresh x i p = ~><~ (π₂ (isupp x)) p

----------------------------------------------------------------------
-- Re-indexing
----------------------------------------------------------------------
infix 5 _↦_
_↦_ : {X : Set}{{_ : lns X}} → ℕ → ℕ → X → X
(i ↦ j)x =
  let a = new (Иe₁ (asupp x)) in
  (j <~ a)((i ~> a)x) -- Equation (22)

↦fresh :
  {X : Set}
  {{_ : lns X}}
  {i j : ℕ}
  (x : X)
  (a : 𝔸)
  {{_ : a # x}}
  → ----------------------------
  (i ↦ j)x ≡ (j <~ a)((i ~> a)x)
↦fresh x a =
  let
    bs = Иe₁ (asupp x)
    b  = new bs
    b#x : b # x
    b#x = Иe₂ (asupp x) b {{unfinite bs}}
  in <~~> b#x it

≻↦ :
  {X : Set}
  {{_ : lns X}}
  (i j : ℕ)
  (x : X)
  → ------------------
  i ≻ x → (i ↦ j)x ≡ x
≻↦ i j x p =
  let
    as = Иe₁ (asupp x)
    a  = new as
    instance
      _ : a # x
      _ = Иe₂ (asupp x) a {{unfinite as}}
  in
  proof
    (i ↦ j)x
  ≡[]
    (j <~ a)((i ~> a)x)
  ≡[ ap (j <~ a) (≻3 p ≤refl) ]
     (j <~ a)x
  ≡[ #2 it ]
    x
  qed

----------------------------------------------------------------------
-- Renset properties of renaming [Proposition 2.17]
----------------------------------------------------------------------
module _ {X : Set}{{_ : lns X}}{x : X} where
  rn₁ : -- Equation (23)
    {a : 𝔸}
    → ----------
    (a ↤ a)x ≡ x
  rn₁ {a} =
    let
      i = π₁ (isupp x)
      i≻x : i ≻ x
      i≻x = π₂(isupp x)
    in
    proof
      (a ↤ a)x
    ≡[]
      (i ~> a)((i <~ a)x)
    ≡[ oc₄ _ _ _ ]
      (i ~> a)x
    ≡[ ≻3 i≻x ≤refl ]
      x
    qed

  rn₂ : -- Equation (24)
    {a b c : 𝔸}
    {{_ : a ≠ c}}
    → --------------------------
    (b ↤ a)((c ↤ a)x) ≡ (c ↤ a)x
  rn₂ {a} {b} {c} =
    proof
      (b ↤ a)((c ↤ a)x)
    ≡[]
      (j ~> b)((j <~ a)((i ~> c)((i <~ a)x)))
    ≡[ ~><~ q (≻1 ≤max₂ q) ]
      (k ~> b)((k <~ a)((i ~> c)((i <~ a)x)))
    ≡[ ap ((k ~> b) ∘ (k <~ a)) (~><~ p (≻1 ≤max₁ p)) ]
      (k ~> b)((k <~ a)((k ~> c)((k <~ a)x)))
    ≡[ ap (k ~> b) (#2 r) ]
      (k ~> b)((k ~> c)((k <~ a)x))
    ≡[ oc₁ _ _ _ _ ]
      (k ~> c)((k <~ a)x)
    ≡[ ~><~ (≻1 ≤max₁ p) p ]
      (c ↤ a)x
    qed
    where
    i = π₁ (isupp x)
    p : i ≻ x
    p = π₂ (isupp x)
    j = π₁ (isupp ((i ~> c)((i <~ a)x)))
    q : j ≻ (i ~> c)((i <~ a)x)
    q = π₂ (isupp ((i ~> c)((i <~ a)x)))
    k = max i j
    A = Иe₁ (asupp x) -- atom-supports x
    s : (A -[ a ]) ∪ [ c ] atom-supports (k ~> c)((k <~ a)x)
    s = ~>atom-supports (<~atom-supports λ a' p' →
      Иe₂ (asupp x) a' {{p'}})
    r : a # (k ~> c)((k <~ a)x)
    r = s a (∉∪{{p = x∉xs-[x] A}}{{∉[]}})

  rn₃ : -- Equation (25)
    {a b c : 𝔸}
    → -----------------------------------
    (c ↤ b)((b ↤ a)x) ≡ (c ↤ a)((c ↤ b)x)
  rn₃ {a} {b} {c} =
    proof
      (c ↤ b)((b ↤ a)x)
    ≡[]
      (j ~> c)((j <~ b)((i ~> b)((i <~ a)x)))
    ≡[ ~><~ q (≻1 (≤trans (≤max₂ {i}) ≤max₁) q) ]
      (k ~> c)((k <~ b)((i ~> b)((i <~ a)x)))
    ≡[ ap ((k ~> c) ∘ (k <~ b))
       (~><~ p (≻1 (≤trans (≤max₁ {i}) ≤max₁) p)) ]
      (k ~> c)((k <~ b)((k ~> b)((k <~ a)x)))
    ≡[ ap (k ~> c) (oc₉ _ _ _ _ _) ]
      (k ~> c)((k <~ a)((k ~> a)((k <~ b)x)))
    ≡[ symm (oc₈ _ _ _ _ _) ]
      (k ~> c)((k <~ a)((k ~> c)((k <~ b)x)))
    ≡[ ap ((k ~> c) ∘ (k <~ a))
      (~><~ (≻1 (≤trans ≤max₁ ≤max₁) p) p) ]
      (k ~> c)((k <~ a)((i ~> c)((i <~ b)x)))
    ≡[ ~><~ (≻1 ≤max₂ q') q' ]
      (j' ~> c)((j' <~ a)((i ~> c)((i <~ b)x)))
    ≡[]
      (c ↤ a)((c ↤ b)x)
    qed
    where
    i = π₁ (isupp x)
    p : i ≻ x
    p = π₂ (isupp x)
    j = π₁ (isupp ((i ~> b)((i <~ a)x)))
    q : j ≻ (i ~> b)((i <~ a)x)
    q = π₂ (isupp ((i ~> b)((i <~ a)x)))
    j' = π₁ (isupp ((i ~> c)((i <~ b)x)))
    q' : j' ≻ (i ~> c)((i <~ b)x)
    q' = π₂ (isupp ((i ~> c)((i <~ b)x)))
    k = max (max i j) j'

  rn₄ : -- Equation (26)
    {a b a' b' : 𝔸}
    {{_ : b  ≠ a'}}
    {{_ : a  ≠ a'}}
    {{_ : b' ≠ a }}
    → ---------------------------------------
    (b ↤ a)((b' ↤ a')x) ≡ (b' ↤ a')((b ↤ a)x)
  rn₄ {a} {b} {a'} {b'} =
    proof
      (b ↤ a)((b' ↤ a')x)
    ≡[]
      (j' ~> b)((j' <~ a)((i ~> b')((i <~ a')x)))
    ≡[ ~><~ q' (≻1 ≤max₂ q') ]
      (k' ~> b)((k' <~ a)((i ~> b')((i <~ a')x)))
    ≡[ ap ((k' ~> b) ∘ (k' <~ a)) (~><~ p (≻1 ≤max₁ p)) ]
      (k' ~> b)((k' <~ a)((k ~> b')((k <~ a')x)))
    ≡[ ap (k' ~> b) (symm (oc₇ _ _ _ _ _ {{symm≠ k' k k'≠k}})) ]
      (k' ~> b)((k ~> b')((k' <~ a)((k <~ a')x)))
    ≡[ oc₅ _ _ _ _ _ {{k'≠k}} ]
      (k ~> b')((k' ~> b)((k' <~ a)((k <~ a')x)))
    ≡[ ap ((k ~> b') ∘ (k' ~> b)) (oc₆ _ _ _ _ _) ]
      (k ~> b')((k' ~> b)((k <~ a')((k' <~ a)x)))
    ≡[ ap (k ~> b') (oc₇ _ _ _ _ _ {{k'≠k}}) ]
      (k ~> b')((k <~ a')((k' ~> b)((k' <~ a)x)))
    ≡[ ap ((k ~> b') ∘ (k <~ a')) (~><~ (≻1 i≤k' p) p) ]
      (k ~> b')((k <~ a')((i ~> b)((i <~ a)x)))
    ≡[ ~><~ (≻1 ≤max₂ q) q ]
      (j ~> b')((j <~ a')((i ~> b)((i <~ a)x)))
    ≡[]
      (b' ↤ a')((b ↤ a)x)
    qed
    where
    i = π₁ (isupp x)
    p : i ≻ x
    p = π₂ (isupp x)
    j = π₁ (isupp ((i ~> b)((i <~ a)x)))
    q : j ≻ (i ~> b)((i <~ a)x)
    q = π₂ (isupp ((i ~> b)((i <~ a)x)))
    j' = π₁ (isupp ((i ~> b')((i <~ a')x)))
    q' : j' ≻ (i ~> b')((i <~ a')x)
    q' = π₂ (isupp ((i ~> b')((i <~ a')x)))
    k = max i j
    k' = max (k +1) j'
    i≤k' : i ≤ k'
    i≤k' = ≤trans (≤max₁{y = j}) (≤trans (≤+1 ≤refl) (≤max₁{y = j'}))
    k'≠k : k' ≠ k
    k'≠k = +1≤→≠ k k' (≤max₁ {y = j'})

----------------------------------------------------------------------
-- Freshness for rensets [Lemma 2.18, Corollary 2.19]
----------------------------------------------------------------------
module _
  {X : Set}
  {{_ : lns X}}
  {x : X}
  {a : 𝔸}
  where
  #→ren# : -- Equation (28), first implication
    (_ : a # x)
    (b : 𝔸)
    → ----------
    (b ↤ a)x ≡ x
  #→ren# a#x b =
    proof
      (b ↤ a) x
    ≡[]
      (i ~> b)((i <~ a)x)
    ≡[ ap (i ~> b) (#2 a#x) ]
      (i ~> b)x
    ≡[ ≻3 p ≤refl ]
      x
    qed
    where
    i = π₁ (isupp x)
    p : i ≻ x
    p = π₂ (isupp x)

  ∀→И : -- Equation (28), second implication
    (∀ b → (b ↤ a)x ≡ x)
    → --------------------
    И b ∶ 𝔸 , (b ↤ a)x ≡ x
  ∀→И p = Иi Ø λ b → p b

  ren#→# : -- Equation (28), third implication
    (_ : И b ∶ 𝔸 , (b ↤ a)x ≡ x)
    → --------------------------
    a # x
  ren#→# p = #3 {a = a}{x}{i}
   (proof
      (i <~ a) x
    ≡[ ap (i <~ a) (symm (≻3 q ≤refl)) ]
      (i <~ a)((i ~> a)x)
    ≡[ ap ((i <~ a) ∘ (i ~> a)) (symm (#2 b#x)) ]
      (i <~ a)((i ~> a)((i <~ b)x))
    ≡[ oc₉ _ _ _ _ _ ]
      (i <~ b)((i ~> b)((i <~ a)x))
    ≡[ ap (i <~ b) (Иe₂ p b {{b∉A}}) ]
      (i <~ b)x
    ≡[ #2 b#x ]
      x
    qed)
    where
    A = Иe₁ p
    b : 𝔸
    b = new (A ∪ Иe₁ (asupp x))
    b#x : b # x
    b#x = Иe₂ (asupp x) b {{∉∪₂ (unfinite (A ∪ Иe₁ (asupp x)))}}
    b∉A : b ∉ A
    b∉A = ∉∪₁ (unfinite (A ∪ Иe₁ (asupp x)))
    i = π₁ (isupp x)
    q : i ≻ x
    q = π₂ (isupp x)

#↤ : -- Corollary 2.19
  {X : Set}
  {{_ : lns X}}
  (x : X)
  (a b c : 𝔸)
  {{_ : c # x}}
  {{_ : c ≠ b}}
  → -----------
  c # (b ↤ a)x
#↤ x a b c with b ≐ a
... | equ rewrite rn₁ {x = x} {a} = it
... | neq f = ren#→# {x = (b ↤ a)x} {c} (Иi [ a ] и₂)
  where
  и₂ :
    (d : 𝔸)
    {{_ : d ∉ [ a ]}}
    → ----------------------------
    (d ↤ c)((b ↤ a) x) ≡ (b ↤ a) x
  и₂ d {{∉[]}} with c ≐ a
  ... | equ = rn₂
  ... | neq g =
    proof
      (d ↤ c)((b ↤ a) x)
    ≡[ rn₄ {a = c} {d} {a} {b} {{it}} {{¬≡→≠ g}} {{symm≠ c b it}} ]
      (b ↤ a)((d ↤ c) x)
    ≡[ ap (b ↤ a) (#→ren# it d) ]
      (b ↤ a) x
    qed

#↤' :
  {X : Set}
  {{_ : lns X}}
  (x : X)
  (a b : 𝔸)
  {{_ : a ≠ b}}
  → -----------
  a # (b ↤ a)x
#↤' x a b = ren#→# (Иi Ø λ _ → rn₂)

ren-supp : -- Remark 2.20
  {X : Set}
  {{_ : lns X}}
  (x : X)
  → ------------------------------
  И a ∶ 𝔸 , И b ∶ 𝔸 , (b ↤ a)x ≡ x
ren-supp x =
  Иi (Иe₁ (asupp x)) λ a → Иi Ø λ b → #→ren# (Иe₂ (asupp x) a) b

----------------------------------------------------------------------
-- Name-name swapping [Equation (29)]
----------------------------------------------------------------------
module _ {X : Set}{{_ : lns X}} where
  infix 5 _≀ₐₐ_
  _≀ₐₐ_ : {X : Set}{{_ : lns X}} → 𝔸 → 𝔸 → X → X
  (a ≀ₐₐ b)x =
    let c = new ([ a ] ∪ [ b ] ∪ Иe₁ (asupp x)) in
    (b ↤ c)((a ↤ b)((c ↤ a)x))

  ≀ₐₐwelldef :
    (a b c c' : 𝔸)
    (x : X)
    {{_ : c # x}}
    {{_ : c ≠ a}}
    {{_ : c ≠ b}}
    {{_ : c' # x}}
    {{_ : c' ≠ a}}
    {{_ : c' ≠ b}}
    → --------------------------
    (b ↤ c)((a ↤ b)((c ↤ a)x)) ≡
    (b ↤ c')((a ↤ b)((c' ↤ a)x))
  ≀ₐₐwelldef a b c c' x with c' ≐ c
  ... | equ = refl
  ... | neq f =
    proof
      (b ↤ c)((a ↤ b)((c ↤ a)x))
    ≡[ ap (b ↤ c) (symm (#→ren# (#↤
      ((c ↤ a)x) b a c' {{#↤ x a c c' {{it}}{{¬≡→≠  f}}}}) b)) ]
      (b ↤ c)((b ↤ c')((a ↤ b)((c ↤ a)x)))
    ≡[ symm rn₃ ]
      (b ↤ c')((c' ↤ c)((a ↤ b)((c ↤ a)x)))
    ≡[ ap (b ↤ c') (rn₄ {a = c} {c'} {b} {a} {{it}}{{it}}{{symm≠ c a it}}) ]
      (b ↤ c')((a ↤ b)((c' ↤ c)((c ↤ a)x)))
    ≡[ ap ((b ↤ c') ∘ (a ↤ b)) rn₃ ]
      (b ↤ c')((a ↤ b)((c' ↤ a)((c' ↤ c)x)))
    ≡[ ap ((b ↤ c') ∘ (a ↤ b) ∘ (c' ↤ a)) (#→ren# it c') ]
      (b ↤ c')((a ↤ b)((c' ↤ a)x))
    qed

  ≀ₐₐfresh :
    (a b c : 𝔸)
    (x : X)
    {{_ : c # x}}
    {{_ : c ≠ a}}
    {{_ : c ≠ b}}
    → -------------------------------------
    (a ≀ₐₐ b)x ≡ (b ↤ c)((a ↤ b)((c ↤ a)x))
  ≀ₐₐfresh  a b c x =
    let
      as = [ a ] ∪ [ b ] ∪ Иe₁ (asupp x)
      d = new as
      instance
        _ : d # x
        _ = Иe₂ (asupp x) d {{∉∪₂ (∉∪₂ (unfinite as))}}
        _ : d ≠ a
        _ = ∉[]₁ (∉∪₁ (unfinite as))
        _ : d ≠ b
        _ = ∉[]₁ (∉∪₁ (∉∪₂ (unfinite as)))
    in ≀ₐₐwelldef a b d c x

  #≀ₐₐ :
    (a b c : 𝔸)
    (x : X)
    {{_ : c # x}}
    {{_ : c ≠ a}}
    {{_ : c ≠ b}}
    → ------------
    c # (a ≀ₐₐ b)x
  #≀ₐₐ a b c x rewrite ≀ₐₐfresh a b c x {{it}}{{it}}{{it}} = #↤' _ c b

  --------------------------------------------------------------------
  -- Properties of name-swapping and renaming [Lemma 2.21]
  --------------------------------------------------------------------
  ts₁ : -- Equation (31)
    {x : X}
    {a : 𝔸}
    → ------------
    (a ≀ₐₐ a)x ≡ x
  ts₁ {x} {a} =
    let
      as = [ a ] ∪ Иe₁ (asupp x)
      c = new as
      instance
        _ : c # x
        _ = Иe₂ (asupp x) c {{∉∪₂ (unfinite as)}}
        _ : c ≠ a
        _ = ∉[]₁ (∉∪₁ (unfinite as))
    in
    proof
      (a ≀ₐₐ a) x
    ≡[ ≀ₐₐfresh a a c x ]
      (a ↤ c)((a ↤ a)((c ↤ a)x))
    ≡[ ap (a ↤ c) rn₁ ]
      (a ↤ c)((c ↤ a)x)
    ≡[ rn₃ ]
      (a ↤ a)((a ↤ c)x)
    ≡[ rn₁ ]
      (a ↤ c)x
    ≡[ #→ren# it a ]
      x
    qed

  ts₂ : -- Equation (32)
    {x : X}
    {a b : 𝔸}
    → -----------------------
    (a ≀ₐₐ b)((a ≀ₐₐ b)x) ≡ x
  ts₂ {x} {a} {b} with  a ≐ b
  ... | equ = ts₁ ； ts₁
  ... | neq f =
    let
      as = [ a ] ∪ [ b ] ∪ Иe₁ (asupp x)
      c = new as
      as' = [ c ] ∪ as
      c' = new as'
      instance
        _ : c' # x
        _ = Иe₂ (asupp x) c' {{∉∪₂ (∉∪₂ (∉∪₂ (unfinite as')))}}
        _ : c' ≠ a
        _ = ∉[]₁ (∉∪₁ (∉∪₂ (unfinite as')))
        _ : c' ≠ b
        _ = ∉[]₁ (∉∪₁ (∉∪₂ (∉∪₂ (unfinite as'))))
        _ : c' # (a ≀ₐₐ b)x
        _ = #≀ₐₐ a b c' x
        _ : c' ≠ c
        _ = ∉[]₁ (∉∪₁(unfinite as'))
        _ : a ≠ c
        _ = symm≠ c a (∉[]₁ (∉∪₁ (unfinite as)))
        _ : b ≠ a
        _ = symm≠ a b (¬≡→≠  f)
        _ : b ≠ c
        _ = symm≠ c b (∉[]₁ (∉∪₁ (∉∪₂ (unfinite as))))
        _ : c # x
        _ = Иe₂ (asupp x) c {{∉∪₂ (∉∪₂ (unfinite as))}}
    in
    proof
      (a ≀ₐₐ b)((a ≀ₐₐ b)x)
    ≡[ ≀ₐₐfresh a b c' ((a ≀ₐₐ b)x) ]
      (b ↤ c')((a ↤ b)((c' ↤ a)((a ≀ₐₐ b)x)))
    ≡[]
      (b ↤ c')((a ↤ b)((c' ↤ a)((b ↤ c)((a ↤ b)((c ↤ a)x)))))
    ≡[ ap ((b ↤ c') ∘ (a ↤ b)) (rn₄ {a = a} {c'} {c} {b}) ]
       (b ↤ c')((a ↤ b)((b ↤ c)((c' ↤ a)((a ↤ b)((c ↤ a)x)))))
    ≡[ ap ((b ↤ c') ∘ (a ↤ b) ∘ (b ↤ c)) rn₃ ]
       (b ↤ c')((a ↤ b)((b ↤ c)((c' ↤ b)((c' ↤ a)((c ↤ a)x)))))
    ≡[ ap ((b ↤ c') ∘ (a ↤ b) ∘ (b ↤ c) ∘ (c' ↤ b))
       (rn₂ {a = a}{c'}{c}) ]
      (b ↤ c')((a ↤ b)((b ↤ c)((c' ↤ b)((c ↤ a)x))))
    ≡[ ap (b ↤ c') rn₃ ]
      (b ↤ c')((a ↤ c)((a ↤ b)((c' ↤ b)((c ↤ a)x))))
    ≡[ ap ((b ↤ c') ∘ (a ↤ c))
       (rn₂ {a = b}{a}{c'} {{symm≠ c' b it}}) ]
      (b ↤ c')((a ↤ c)((c' ↤ b)((c ↤ a)x)))
    ≡[ rn₄ {a = c'} {b} {c} {a} {{it}}{{it}}{{symm≠ c' a it}} ]
      (a ↤ c)((b ↤ c')((c' ↤ b)((c ↤ a)x)))
    ≡[ ap (a ↤ c) rn₃ ]
      (a ↤ c)((b ↤ b)((b ↤ c')((c ↤ a)x)))
    ≡[ ap (a ↤ c) rn₁ ]
      (a ↤ c)((b ↤ c')((c ↤ a)x))
    ≡[ rn₄ {a = c} {a} {c'} {b} {{symm≠ c' a it}} {{symm≠ c' c it}} ]
      (b ↤ c')((a ↤ c)((c ↤ a)x))
    ≡[ ap (b ↤ c') rn₃ ]
      (b ↤ c')((a ↤ a)((a ↤ c)x))
    ≡[ ap (b ↤ c') rn₁ ]
      (b ↤ c')((a ↤ c)x)
    ≡[ ap (b ↤ c') (#→ren# it a) ]
      (b ↤ c')x
    ≡[ #→ren# it b ]
      x
    qed

  ts₃ : -- Equation (33)
    {x : X}
    {a b c d : 𝔸}
    {{_ : b ≠ c}}
    {{_ : c ≠ a}}
    {{_ : a ≠ d}}
    {{_ : d ≠ b}}
    → -------------------------------------------
    (a ≀ₐₐ b)((c ≀ₐₐ d)x) ≡ (c ≀ₐₐ d)((a ≀ₐₐ b)x)
  ts₃ {x} {a} {b} {c} {d} =
    let
      as = [ a ] ∪ [ b ] ∪ [ c ] ∪ [ d ] ∪ Иe₁ (asupp x)
      e = new as
      as' = [ e ] ∪ as
      e' = new as'
      instance
        _ : e # x
        _ = Иe₂ (asupp x) e {{∉∪₂ (∉∪₂ (∉∪₂ (∉∪₂ (unfinite as))))}}
        _ : e ≠ a
        _ = ∉[]₁ (∉∪₁ (unfinite as))
        _ : e ≠ b
        _ = ∉[]₁ (∉∪₁ (∉∪₂ (unfinite as)))
        _ : e ≠ c
        _ = ∉[]₁ (∉∪₁ (∉∪₂ (∉∪₂ (unfinite as))))
        _ : e ≠ d
        _ = ∉[]₁ (∉∪₁ (∉∪₂ (∉∪₂ (∉∪₂ (unfinite as)))))
        _ : e # (c ≀ₐₐ d)x
        _ = #≀ₐₐ c d e x
        _ : e' # x
        _ = Иe₂ (asupp x) e' {{∉∪₂ (∉∪₂ (∉∪₂ (∉∪₂ (∉∪₂ (unfinite as')))))}}
        _ : e' ≠ a
        _ = ∉[]₁ (∉∪₁ (∉∪₂ (unfinite as')))
        _ : e' ≠ b
        _ = ∉[]₁ (∉∪₁ (∉∪₂ (∉∪₂ (unfinite as'))))
        _ : e' ≠ c
        _ = ∉[]₁ (∉∪₁ (∉∪₂ (∉∪₂ (∉∪₂ (unfinite as')))))
        _ : e' ≠ d
        _ = ∉[]₁ (∉∪₁ (∉∪₂ (∉∪₂ (∉∪₂ (∉∪₂ (unfinite as'))))))
        _ : e' # (a ≀ₐₐ b)x
        _ = #≀ₐₐ a b e' x
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
      (a ≀ₐₐ b)((c ≀ₐₐ d)x)
    ≡[ ≀ₐₐfresh a b e ((c ≀ₐₐ d)x) ]
      (b ↤ e)((a ↤ b)((e ↤ a)((c ≀ₐₐ d)x)))
    ≡[ ap ((b ↤ e) ∘ (a ↤ b) ∘ (e ↤ a)) (≀ₐₐfresh c d e' x) ]
      (b ↤ e)((a ↤ b)((e ↤ a)((d ↤ e')((c ↤ d)((e' ↤ c)x)))))
    ≡[ ap ((b ↤ e) ∘ (a ↤ b)) (rn₄ {a = a} {e} {e'} {d}) ]
      (b ↤ e)((a ↤ b)((d ↤ e')((e ↤ a)((c ↤ d)((e' ↤ c)x)))))
    ≡[ ap (b ↤ e) (rn₄ {a = b} {a} {e'} {d} ) ]
      (b ↤ e)((d ↤ e')((a ↤ b)((e ↤ a)((c ↤ d)((e' ↤ c)x)))))
    ≡[ rn₄ {a = e} {b} {e'} {d} ]
      (d ↤ e')((b ↤ e)((a ↤ b)((e ↤ a)((c ↤ d)((e' ↤ c)x)))))
    ≡[ ap ((d ↤ e') ∘ (b ↤ e) ∘ (a ↤ b)) (rn₄ {a = a} {e} {d} {c}) ]
      (d ↤ e')((b ↤ e)((a ↤ b)((c ↤ d)((e ↤ a)((e' ↤ c)x)))))
    ≡[ ap ((d ↤ e') ∘ (b ↤ e)) (rn₄ {a = b} {a} {d} {c}) ]
      (d ↤ e')((b ↤ e)((c ↤ d)((a ↤ b)((e ↤ a)((e' ↤ c)x)))))
    ≡[ ap (d ↤ e') (rn₄ {a = e} {b} {d} {c}) ]
      (d ↤ e')((c ↤ d)((b ↤ e)((a ↤ b)((e ↤ a)((e' ↤ c)x)))))
    ≡[ ap ((d ↤ e') ∘ (c ↤ d) ∘ (b ↤ e) ∘ (a ↤ b)) (rn₄ {a = a} {e} {c} {e'}) ]
      (d ↤ e')((c ↤ d)((b ↤ e)((a ↤ b)((e' ↤ c)((e ↤ a)x)))))
    ≡[ ap ((d ↤ e') ∘ (c ↤ d) ∘ (b ↤ e)) (rn₄ {a = b} {a} {c} {e'}) ]
      (d ↤ e')((c ↤ d)((b ↤ e)((e' ↤ c)((a ↤ b)((e ↤ a)x)))))
    ≡[ ap ((d ↤ e') ∘ (c ↤ d)) (rn₄ {a = e} {b} {c} {e'}) ]
      (d ↤ e')((c ↤ d)((e' ↤ c)((b ↤ e)((a ↤ b)((e ↤ a)x)))))
    ≡[ ap ((d ↤ e') ∘ (c ↤ d) ∘ (e' ↤ c)) (symm (≀ₐₐfresh a b e x)) ]
      (d ↤ e')((c ↤ d)((e' ↤ c)((a ≀ₐₐ b)x)))
    ≡[ symm (≀ₐₐfresh c d e' ((a ≀ₐₐ b)x)) ]
      (c ≀ₐₐ d)((a ≀ₐₐ b)x)
    qed

  ts₄ : -- Equation (34)
    {x : X}
    {a b c : 𝔸}
    {{_ : b ≠ c}}
    {{_ : c ≠ a}}
    → -------------------------------------------
    (a ≀ₐₐ b)((c ≀ₐₐ a)x) ≡ (c ≀ₐₐ b)((a ≀ₐₐ b)x)
  ts₄ {x} {a} {b} {c} with b ≐ a
  ... | equ =
    proof
      (a ≀ₐₐ a)((c ≀ₐₐ a)x)
    ≡[ ts₁ ]
      (c ≀ₐₐ a)x
    ≡[ ap (c ≀ₐₐ a) (symm ts₁) ]
      (c ≀ₐₐ a)((a ≀ₐₐ a)x)
    qed
  ... | neq f =
    let
      as = [ a ] ∪ [ b ] ∪ [ c ] ∪ Иe₁ (asupp x)
      e = new as
      as' = [ e ] ∪ as
      e' = new as'
      instance
        _ : e # x
        _ = Иe₂ (asupp x) e {{∉∪₂ (∉∪₂ (∉∪₂ (unfinite as)))}}
        _ : e ≠ a
        _ = ∉[]₁ (∉∪₁ (unfinite as))
        _ : e ≠ b
        _ = ∉[]₁ (∉∪₁ (∉∪₂ (unfinite as)))
        _ : e ≠ c
        _ = ∉[]₁ (∉∪₁ (∉∪₂ (∉∪₂ (unfinite as))))
        _ : e # (c ≀ₐₐ a)x
        _ = #≀ₐₐ c a e x
        _ : e' # x
        _ = Иe₂ (asupp x) e' {{∉∪₂ (∉∪₂ (∉∪₂ (∉∪₂ (unfinite as'))))}}
        _ : e' ≠ c
        _ = ∉[]₁ (∉∪₁ (∉∪₂ (∉∪₂ (∉∪₂ (unfinite as')))))
        _ : e' ≠ a
        _ = ∉[]₁ (∉∪₁ (∉∪₂ (unfinite as')))
        _ : e' # x
        _ = Иe₂ (asupp x) e' {{∉∪₂ (∉∪₂ (∉∪₂ (∉∪₂ (unfinite as'))))}}
        _ : e' ≠ a
        _ = ∉[]₁ (∉∪₁ (∉∪₂ (unfinite as')))
        _ : e' ≠ b
        _ = ∉[]₁ (∉∪₁ (∉∪₂ (∉∪₂ (unfinite as'))))
        _ : e # (a ≀ₐₐ b)x
        _ = #≀ₐₐ a b e x
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
      (a ≀ₐₐ b)((c ≀ₐₐ a)x)
    ≡[ ≀ₐₐfresh a b e ((c ≀ₐₐ a)x) ]
      (b ↤ e)((a ↤ b)((e ↤ a)((c ≀ₐₐ a)x)))
    ≡[ ap ((b ↤ e) ∘ (a ↤ b) ∘ (e ↤ a)) (≀ₐₐfresh c a e' x) ]
      (b ↤ e)((a ↤ b)((e ↤ a)((a ↤ e')((c ↤ a)((e' ↤ c)x)))))
    ≡[ ap ((b ↤ e) ∘ (a ↤ b)) rn₃ ]
      (b ↤ e)((a ↤ b)((e ↤ e')((e ↤ a)((c ↤ a)((e' ↤ c)x)))))
    ≡[ ap ((b ↤ e) ∘ (a ↤ b) ∘ (e ↤ e')) (rn₂ {a = a} {e} {c}) ]
      (b ↤ e)((a ↤ b)((e ↤ e')((c ↤ a)((e' ↤ c)x))))
    ≡[ ap ((b ↤ e) ∘ (a ↤ b)) (rn₄ {a = e'} {e} {a} {c}) ]
      (b ↤ e)((a ↤ b)((c ↤ a)((e ↤ e')((e' ↤ c)x))))
    ≡[ ap ((b ↤ e) ∘ (a ↤ b) ∘ (c ↤ a)) rn₃ ]
      (b ↤ e)((a ↤ b)((c ↤ a)((e ↤ c)((e ↤ e')x))))
    ≡[ ap ((b ↤ e) ∘ (a ↤ b) ∘ (c ↤ a) ∘ (e ↤ c)) (#→ren# it e) ]
      (b ↤ e)((a ↤ b)((c ↤ a)((e ↤ c)x)))
    ≡[ ap ((b ↤ e) ∘ (a ↤ b) ∘ (c ↤ a)) (symm (#→ren# (#↤ x c e e') c)) ]
      (b ↤ e)((a ↤ b)((c ↤ a)((c ↤ e')((e ↤ c)x))))
    ≡[ ap ((b ↤ e) ∘ (a ↤ b)) (symm rn₃) ]
      (b ↤ e)((a ↤ b)((c ↤ e')((e' ↤ a)((e ↤ c)x))))
    ≡[ ap (b ↤ e) (symm (rn₄ {a = e'} {c} {b} {a})) ]
      (b ↤ e)((c ↤ e')((a ↤ b)((e' ↤ a)((e ↤ c)x))))
    ≡[ ap ((b ↤ e) ∘ (c ↤ e')) (symm (rn₂ {a = b} {c} {a})) ]
      (b ↤ e)((c ↤ e')((c ↤ b)((a ↤ b)((e' ↤ a)((e ↤ c)x)))))
    ≡[ ap ((b ↤ e) ∘ (c ↤ e') ∘ (c ↤ b) ∘ (a ↤ b)) (symm (rn₄ {a = c} {e} {a} {e'})) ]
      (b ↤ e)((c ↤ e')((c ↤ b)((a ↤ b)((e ↤ c)((e' ↤ a)x)))))
    ≡[ ap ((b ↤ e) ∘ (c ↤ e') ∘ (c ↤ b)) (symm (rn₄ {a = c} {e} {b} {a})) ]
      (b ↤ e)((c ↤ e')((c ↤ b)((e ↤ c)((a ↤ b)((e' ↤ a)x)))))
    ≡[ ap (b ↤ e) (symm rn₃) ]
      (b ↤ e)((c ↤ b)((b ↤ e')((e ↤ c)((a ↤ b)((e' ↤ a)x)))))
    ≡[ ap ((b ↤ e) ∘ (c ↤ b)) (symm (rn₄ {a = c} {e} {e'} {b})) ]
      (b ↤ e)((c ↤ b)((e ↤ c)((b ↤ e')((a ↤ b)((e' ↤ a)x)))))
    ≡[ ap ((b ↤ e) ∘ (c ↤ b) ∘ (e ↤ c)) (symm (≀ₐₐfresh a b e' x)) ]
      (b ↤ e)((c ↤ b)((e ↤ c)((a ≀ₐₐ b)x)))
    ≡[ symm (≀ₐₐfresh c b e ((a ≀ₐₐ b)x)) ]
      (c ≀ₐₐ b)((a ≀ₐₐ b)x)
    qed

  ts₅ : -- Equation (35)
    {x : X}
    {a b c : 𝔸}
    {{_ : b ≠ c}}
    → -------------------------------------
    (c ↤ b)((a ≀ₐₐ b)x) ≡ (a ↤ b)((c ↤ a)x)
  ts₅ {x} {a} {b} {c} with b ≐ a
  ... | equ =
    proof
      (c ↤ a)((a ≀ₐₐ a)x)
    ≡[ ap (c ↤ a) ts₁ ]
      (c ↤ a)x
    ≡[ symm rn₁ ]
      (a ↤ a)((c ↤ a)x)
    qed
  ... | neq f =
    let
      as = [ a ] ∪ [ b ] ∪ [ c ] ∪ Иe₁ (asupp x)
      d = new as
      instance
        _ : d # x
        _ = Иe₂ (asupp x) d {{∉∪₂ (∉∪₂ (∉∪₂ (unfinite as)))}}
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
    in
    proof
      (c ↤ b)((a ≀ₐₐ b)x)
    ≡[ ap (c ↤ b) (≀ₐₐfresh a b d x) ]
      (c ↤ b)((b ↤ d)((a ↤ b)((d ↤ a)x)))
    ≡[ rn₃  ]
      (c ↤ d)((c ↤ b)((a ↤ b)((d ↤ a)x)))
    ≡[ ap (c ↤ d) (rn₂ {a = b} {c} {a}) ]
      (c ↤ d)((a ↤ b)((d ↤ a)x))
    ≡[ rn₄ {a = d} {c} {b} {a} ]
      (a ↤ b)((c ↤ d)((d ↤ a)x))
    ≡[ ap (a ↤ b) rn₃ ]
      (a ↤ b)((c ↤ a)((c ↤ d)x))
    ≡[ ap ((a ↤ b) ∘ (c ↤ a)) (#→ren# it c) ]
      (a ↤ b)((c ↤ a)x)
    qed

  ts₆ : -- Equation (36)
    {x : X}
    {a b c d : 𝔸}
    {{_ : b ≠ c}}
    {{_ : c ≠ a}}
    {{_ : a ≠ d}}
    {{_ : d ≠ b}}
    → ---------------------------------------
    (a ≀ₐₐ b)((d ↤ c)x) ≡ (d ↤ c)((a ≀ₐₐ b)x)
  ts₆ {x} {a} {b} {c} {d} =
    let
      as = [ a ] ∪ [ b ] ∪ [ c ] ∪ [ d ] ∪ Иe₁ (asupp x)
      e = new as
      instance
        _ : e # x
        _ = Иe₂ (asupp x) e {{∉∪₂ (∉∪₂ (∉∪₂ (∉∪₂ (unfinite as))))}}
        _ : e ≠ a
        _ = ∉[]₁ (∉∪₁ (unfinite as))
        _ : e ≠ b
        _ = ∉[]₁ (∉∪₁ (∉∪₂ (unfinite as)))
        _ : e ≠ c
        _ =  ∉[]₁ (∉∪₁ (∉∪₂ (∉∪₂ (unfinite as))))
        _ : e ≠ d
        _ = ∉[]₁ (∉∪₁ (∉∪₂ (∉∪₂ (∉∪₂ (unfinite as)))))
        _ : e # (d ↤ c)x
        _ = #↤ x c d e
        _ : a ≠ c
        _ = symm≠ c a it
        _ : d ≠ a
        _ = symm≠ a d it
        _ : d ≠ e
        _ = symm≠ e d it
    in
    proof
      (a ≀ₐₐ b)((d ↤ c)x)
    ≡[ ≀ₐₐfresh a b e ((d ↤ c)x) ]
      (b ↤ e)((a ↤ b)((e ↤ a)((d ↤ c)x)))
    ≡[ ap ((b ↤ e) ∘ (a ↤ b)) (rn₄ {a = a} {e} {c} {d}) ]
      (b ↤ e)((a ↤ b)((d ↤ c)((e ↤ a)x)))
    ≡[ ap (b ↤ e) (rn₄ {a = b} {a} {c} {d}) ]
      (b ↤ e)((d ↤ c)((a ↤ b)((e ↤ a)x)))
    ≡[ rn₄ {a = e} {b} {c} {d} ]
      (d ↤ c)((b ↤ e)((a ↤ b)((e ↤ a)x)))
    ≡[ ap (d ↤ c) (symm (≀ₐₐfresh a b e x)) ]
      (d ↤ c)((a ≀ₐₐ b)x)
    qed

  ts₇ : -- Equation (37)
    {x : X}
    {a b c : 𝔸}
    {{_ : b ≠ c}}
    {{_ : c ≠ a}}
    → ---------------------------------------
    (a ≀ₐₐ b)((a ↤ c)x) ≡ (b ↤ c)((a ≀ₐₐ b)x)
  ts₇ {x} {a} {b} {c} =
    let
      as = [ a ] ∪ [ b ] ∪ [ c ] ∪ Иe₁ (asupp x)
      d = new as
      instance
        _ : d # x
        _ = Иe₂ (asupp x) d {{∉∪₂ (∉∪₂ (∉∪₂ (unfinite as)))}}
        _ : d ≠ a
        _ = ∉[]₁ (∉∪₁ (unfinite as))
        _ : d ≠ b
        _ = ∉[]₁ (∉∪₁ (∉∪₂ (unfinite as)))
        _ : d ≠ c
        _ =  ∉[]₁ (∉∪₁ (∉∪₂ (∉∪₂ (unfinite as))))
        _ : d # (a ↤ c)x
        _ = #↤ x c a d
        _ :  a ≠ c
        _ = symm≠ c a it
    in
    proof
      (a ≀ₐₐ b)((a ↤ c)x)
    ≡[ ≀ₐₐfresh a b d ((a ↤ c)x) ]
      (b ↤ d)((a ↤ b)((d ↤ a)((a ↤ c)x)))
    ≡[ ap ((b ↤ d) ∘ (a ↤ b)) rn₃ ]
      (b ↤ d)((a ↤ b)((d ↤ c)((d ↤ a)x)))
    ≡[ ap (b ↤ d) (rn₄ {a = b} {a} {c} {d}) ]
      (b ↤ d)((d ↤ c)((a ↤ b)((d ↤ a)x)))
    ≡[ rn₃ ]
      (b ↤ c)((b ↤ d)((a ↤ b)((d ↤ a)x)))
    ≡[ ap (b ↤ c) (symm (≀ₐₐfresh a b d x)) ]
      (b ↤ c)((a ≀ₐₐ b)x)
    qed

  ts₈ : -- Equation (38)
    {x : X}
    {a b c : 𝔸}
    {{_ : b ≠ c}}
    {{_ : c ≠ a}}
    → ---------------------------------------
    (a ≀ₐₐ b)((c ↤ a)x) ≡ (c ↤ b)((a ≀ₐₐ b)x)
  ts₈ {x} {a} {b} {c} with b ≐ a
  ... | equ =
    proof
      (a ≀ₐₐ a)((c ↤ a)x)
    ≡[ ts₁ ]
      (c ↤ a)x
    ≡[ ap (c ↤ a) (symm ts₁) ]
      (c ↤ a)((a ≀ₐₐ a)x)
    qed
  ... | neq f =
    let
      as = [ a ] ∪ [ b ] ∪ [ c ] ∪ Иe₁ (asupp x)
      d = new as
      instance
        _ : d # x
        _ = Иe₂ (asupp x) d {{∉∪₂ (∉∪₂ (∉∪₂ (unfinite as)))}}
        _ : d ≠ a
        _ = ∉[]₁ (∉∪₁ (unfinite as))
        _ : d ≠ b
        _ = ∉[]₁ (∉∪₁ (∉∪₂ (unfinite as)))
        _ : d ≠ c
        _ =  ∉[]₁ (∉∪₁ (∉∪₂ (∉∪₂ (unfinite as))))
        _ : d # (c ↤ a)x
        _ = #↤ x a c d
        _ :  a ≠ c
        _ = symm≠ c a it
        _ : d # (a ↤ b)((c ↤ a)x)
        _ = #↤ _ b a d
        _ : b ≠ a
        _ = ¬≡→≠  f
        _ : c ≠ b
        _ = symm≠ b c it
        _ : a ≠ d
        _ = symm≠ d a it
    in
    proof
      (a ≀ₐₐ b)((c ↤ a)x)
    ≡[ ≀ₐₐfresh a b d ((c ↤ a)x) ]
      (b ↤ d)((a ↤ b)((d ↤ a)((c ↤ a)x)))
    ≡[ ap ((b ↤ d) ∘ (a ↤ b)) (rn₂ {a = a} {d} {c}) ]
      (b ↤ d)((a ↤ b)((c ↤ a)x))
    ≡[ #→ren# it b ]
      (a ↤ b)((c ↤ a)x)
    ≡[ ap ((a ↤ b) ∘ (c ↤ a)) (symm (#→ren# it c)) ]
      (a ↤ b)((c ↤ a)((c ↤ d)x))
    ≡[ ap (a ↤ b) (symm rn₃) ]
      (a ↤ b)((c ↤ d)((d ↤ a)x))
    ≡[ symm (rn₄ {a = d} {c} {b} {a}) ]
      (c ↤ d)((a ↤ b)((d ↤ a)x))
    ≡[ ap (c ↤ d) (symm (rn₂ {a = b}{c}{a})) ]
      (c ↤ d)((c ↤ b)((a ↤ b)((d ↤ a)x)))
    ≡[ symm rn₃ ]
      (c ↤ b)((b ↤ d)((a ↤ b)((d ↤ a)x)))
    ≡[ ap (c ↤ b) (symm (≀ₐₐfresh a b d x)) ]
      (c ↤ b)((a ≀ₐₐ b)x)
    qed

  ts₉ : -- Equation (39)
    {x : X}
    {a b : 𝔸}
    → ---------------------------------------
    (a ≀ₐₐ b)((b ↤ a)x) ≡ (a ↤ b)((a ≀ₐₐ b)x)
  ts₉ {x} {a} {b} with  b ≐ a
  ... | equ =
    proof
      (a ≀ₐₐ a)((a ↤ a)x)
    ≡[ ts₁ ]
      (a ↤ a)x
    ≡[ ap (a ↤ a) (symm ts₁) ]
      (a ↤ a)((a ≀ₐₐ a)x)
    qed
  ... | neq f =
    let
      as = [ a ] ∪ [ b ] ∪ Иe₁ (asupp x)
      c = new as
      instance
        _ : c # x
        _ = Иe₂ (asupp x) c {{∉∪₂ (∉∪₂ (unfinite as))}}
        _ : c ≠ a
        _ = ∉[]₁ (∉∪₁ (unfinite as))
        _ : c ≠ b
        _ = ∉[]₁ (∉∪₁ (∉∪₂ (unfinite as)))
        _ : c # (b ↤ a)x
        _ = #↤ x a b c
        _ : b ≠ a
        _ = ¬≡→≠  f
        _ : a ≠ b
        _ = symm≠ b a it
        _ : c # (a ↤ b)x
        _ = #↤ x b a c
        _ : a ≠ c
        _ = symm≠ c a it
    in
    proof
      (a ≀ₐₐ b)((b ↤ a)x)
    ≡[ ≀ₐₐfresh a b c ((b ↤ a)x) ]
      (b ↤ c)((a ↤ b)((c ↤ a)((b ↤ a)x)))
    ≡[ ap ((b ↤ c) ∘ (a ↤ b)) (rn₂ {a = a} {c} {b}) ]
      (b ↤ c)((a ↤ b)((b ↤ a)x))
    ≡[ ap (b ↤ c) rn₃ ]
      (b ↤ c)((a ↤ a)((a ↤ b)x))
    ≡[ ap (b ↤ c) rn₁ ]
      (b ↤ c)((a ↤ b)x)
    ≡[ #→ren# it b ]
      (a ↤ b)x
    ≡[ ap (a ↤ b) (symm (#→ren# it a)) ]
      (a ↤ b)((a ↤ c)x)
    ≡[ ap (a ↤ b) (symm rn₁) ]
      (a ↤ b)((a ↤ a)((a ↤ c)x))
    ≡[ ap (a ↤ b) (symm rn₃) ]
      (a ↤ b)((a ↤ c)((c ↤ a)x))
    ≡[ symm (rn₄ {a = c} {a} {b} {a}) ]
      (a ↤ c)((a ↤ b)((c ↤ a)x))
    ≡[ ap (a ↤ c) (symm (rn₂ {a = b} {a} {a})) ]
      (a ↤ c)((a ↤ b)((a ↤ b)((c ↤ a)x)))
    ≡[ symm rn₃ ]
      (a ↤ b)((b ↤ c)((a ↤ b)((c ↤ a)x)))
    ≡[ ap (a ↤ b) (symm (≀ₐₐfresh a b c x)) ]
      (a ↤ b)((a ≀ₐₐ b)x)
    qed
