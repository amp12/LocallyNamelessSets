module Prelude where

------------------------------------------------------------------------
-- Universe levels
------------------------------------------------------------------------
open import Agda.Primitive public

ℓ₀ : Level
ℓ₀ = lzero

ℓ₁ : Level
ℓ₁ = lsuc ℓ₀

ℓ₂ : Level
ℓ₂ = lsuc ℓ₁

----------------------------------------------------------------------
-- Instance
----------------------------------------------------------------------
it : {l : Level} {A : Set l} → {{A}} → A
it {{x}} = x

----------------------------------------------------------------------
-- Case expressions
----------------------------------------------------------------------
case :
  {l m : Level}
  {A : Set l}
  {B : A → Set m}
  (x : A)
  (f : (x : A) → B x)
  → -----------------
  B x
case x f  = f x

---------------------------------------------------------------------
-- Identity function
----------------------------------------------------------------------
id :
  {l : Level}
  {A : Set l}
  → ---------
  A → A
id x = x

----------------------------------------------------------------------
-- Composition
----------------------------------------------------------------------
infixr 5 _∘_
_∘_ :
  {l m n : Level}
  {A : Set l}
  {B : A → Set m}
  {C : (x : A) → B x → Set n}
  (g : {x : A}(y : B x) → C x y)
  (f : (x : A) → B x)
  → ----------------------------
  (x : A) → C x (f x)
(g ∘ f) x = g (f x)

----------------------------------------------------------------------
-- Empty type
----------------------------------------------------------------------
data 𝟘 {l : Level} : Set l where

𝟘e :
  {l m : Level}
  {A : 𝟘 {l} → Set m}
  → -----------------
  ∀ x → A x
𝟘e ()

infix 1 ¬_
¬_ : {l : Level} → Set l → Set l
¬_ {l} p = p → 𝟘{l}

----------------------------------------------------------------------
-- Unit type
----------------------------------------------------------------------
record 𝟙 {ℓ : Level} : Set ℓ where
  instance constructor tt

{-# BUILTIN UNIT 𝟙 #-}

----------------------------------------------------------------------
-- Booleans
----------------------------------------------------------------------
data 𝔹 : Set where
  true false : 𝔹

{-# BUILTIN BOOL  𝔹  #-}
{-# BUILTIN TRUE  true  #-}
{-# BUILTIN FALSE false #-}

--Boolean conditional
infix 0 if_then_else_
if_then_else_ :
  {l : Level}
  {A : 𝔹 → Set l}
  (b : 𝔹)
  → --------------------
  A true → A false → A b
if true  then t else f = t
if false then t else f = f

-- Boolean conjunction
infixr 6 _and_
_and_ : 𝔹 → 𝔹 → 𝔹
true  and true  = true
false and _     = false
_     and false = false

-- Boolean negation
not : 𝔹 → 𝔹
not true = false
not false = true

----------------------------------------------------------------------
-- Homogeneous propositional equality
----------------------------------------------------------------------
infix 4 _≡_
data _≡_ {l : Level}{A : Set l}(x : A) : A → Set l where
  instance refl : x ≡ x

{-# BUILTIN EQUALITY _≡_ #-}

----------------------------------------------------------------------
-- Properties of equality
----------------------------------------------------------------------
ap :
  {l m : Level}
  {A : Set l}
  {B : Set m}
  (f : A → B)
  {x y : A}
  (_ : x ≡ y)
  → -----------
  f x ≡ f y
ap _ refl = refl

ap₂ :
  {l m n : Level}
  {A : Set l}
  {B : Set m}
  {C : Set n}
  (f : A → B → C)
  {x x' : A}
  (_ : x ≡ x')
  {y y' : B}
  (_ : y ≡ y')
  → -------------
  f x y ≡ f x' y'
ap₂ f refl refl = refl

infixl 5 _；_
_；_ :
  {l : Level}
  {A : Set l}
  {x y  z : A}
  (p : x ≡ y)
  (q : y ≡ z)
  → ----------
  x ≡ z
p ； refl = p

symm :
  {l : Level}
  {A : Set l}
  {x y : A}
  (p : x ≡ y)
  → ---------
  y ≡ x
symm refl = refl

symm¬≡ :
  {l : Level}
  {A : Set l}
  {x y : A}
  (p : ¬ x ≡ y)
  → -----------
  ¬ y ≡ x
symm¬≡ p refl = p refl

infix  1 proof_
proof_ :
  {l : Level}
  {A : Set l}
  {x y : A}
  → -----------
  x ≡ y → x ≡ y
proof p = p

infixr 2 _≡[_]_
_≡[_]_ :
  {l : Level}
  {A : Set l}
  (x : A)
  {y z : A}
  → -------------------
  x ≡ y → y ≡ z → x ≡ z
_ ≡[ refl ] q = q

infixr 2 _≡[]_
_≡[]_ :
  {l : Level}
  {A : Set l}
  (x : A)
  {y : A}
  → -----------
  x ≡ y → x ≡ y
_ ≡[] q = q

infix  3 _qed
_qed :
  {l : Level}
  {A : Set l}
  (x : A)
  → ---------
  x ≡ x
_ qed = refl

coe : {l : Level}{P Q : Set l} → P ≡ Q → P → Q
coe refl x = x

subst :
  {l m : Level}
  {A : Set l}
  (B : A → Set m)
  {x x' : A}
  (_ : x ≡ x')
  → -------------
  B x → B x'
subst B refl x = x

uip :
  {l : Level}
  {A : Set l}
  {x x' : A}
  {p : x ≡ x'}
  {p' : x ≡ x'}
  → -----------
  p ≡ p'
uip {p = refl} {refl} = refl

----------------------------------------------------------------------
-- Injective functions
----------------------------------------------------------------------
injection :
  {l m : Level}
  {A : Set l}
  {B : Set m}
  (f : A → B)
  → -----------
  Set (l ⊔ m)
injection f = ∀{x x'} → f x ≡ f x' → x ≡ x'

----------------------------------------------------------------------
-- Subsingletons
----------------------------------------------------------------------
record isProp {l : Level}(A : Set l) : Set l where
  constructor mk!
  field
    ! : (x x' : A) → x ≡ x'

open isProp {{...}} public

----------------------------------------------------------------------
-- Disjoint union
----------------------------------------------------------------------
infixr 6 _⊎_
data _⊎_ {l m : Level}(A : Set l)(B : Set m) : Set (l ⊔ m) where
  ι₁ : (x : A) → A ⊎ B
  ι₂ : (y : B) → A ⊎ B

injectionι₁ :
  {l m : Level}
  {A : Set l}
  {B : Set m}
  → -----------------------
  injection (ι₁ {A = A}{B})
injectionι₁ refl = refl

injectionι₂ :
  {l m : Level}
  {A : Set l}
  {B : Set m}
  → -----------------------
  injection (ι₂ {A = A}{B})
injectionι₂ refl = refl

----------------------------------------------------------------------
-- Recursion over well-founded relations
----------------------------------------------------------------------
module wf {l m : Level}{A : Set l}(R : A → A → Set m) where
  -- Accessibility predicate
  data Acc (x : A) : Set (l ⊔ m) where
    acc : (∀ y → R y x → Acc y) → Acc x

  -- Well-founded relation
  iswf : Set (l ⊔ m)
  iswf = ∀ x → Acc x

  -- Well-founded recursion
  module _
    (w : iswf)
    {n : Level}
    (B : A → Set n)
    (b : ∀ x → (∀ y → R y x → B y) → B x)
    where
    private
      Acc→B : ∀ x → Acc x → B x
      Acc→B x (acc a) = b x (λ y r → Acc→B  y (a y r))

    rec : ∀ x → B x
    rec x = Acc→B x (w x)

  -- Irreflexivity
  irrefl :
    (_ : iswf)
    → ------------------
    ∀ x → R x x → 𝟘 {l}
  irrefl w x p = ¬Accx (w x)
    where
    ¬Accx : Acc x → 𝟘
    ¬Accx (acc f) = ¬Accx (f x p)

----------------------------------------------------------------------
-- Decidable properties
----------------------------------------------------------------------

{- See agda-stdlib/src/Relation/Nullary.aga -}

-- `Reflects` idiom
-- (The truth value of P is reflected by a boolean value)
data Reflects {l : Level}(P : Set l) : 𝔹 → Set l where
  of-y : ( p : P  ) → Reflects P true
  of-n : (¬p : ¬ P) → Reflects P false

invert :
 {l : Level}
 {P : Set l}
 {b : 𝔹}
 → ---------------------------------
 Reflects P b → if b then P else ¬ P
invert (of-y  p) = p
invert (of-n ¬p) = ¬p

-- Decidability.
record Dec {l : Level}(P : Set l) : Set l where
  constructor _because_
  field
    does : 𝔹
    bcos : Reflects P does

open Dec public

pattern yes p = true  because of-y  p
pattern no ¬p = false because of-n ¬p

dec-true :
  {l : Level}
  {P : Set l}
  (p? : Dec P)
  → ----------------
  P → does p? ≡ true
dec-true (true  because   _ ) p = refl
dec-true (false because [¬p]) p with () ← invert [¬p] p

dec-false :
  {l : Level}
  {P : Set l}
  (p? : Dec P)
  → -------------------
  ¬ P → does p? ≡ false
dec-false (false because  _ ) ¬p = refl
dec-false (true  because [p]) ¬p with () ← ¬p (invert [p])

map′ :
  {l : Level}
  {P Q : Set l}
  → -------------------------------
  (P → Q) → (Q → P) → Dec P → Dec Q
does (map′ P→Q Q→P p?)                   = does p?
bcos (map′ P→Q Q→P (true  because [p] )) = of-y (P→Q (invert [p]))
bcos (map′ P→Q Q→P (false because [¬p])) = of-n (invert [¬p] ∘ Q→P)

----------------------------------------------------------------------
-- Decidable homogeneous equality
----------------------------------------------------------------------
record hasDecEq {l : Level}(A : Set l) : Set l where
  constructor mkDecEq
  infix 4 _≐_
  field _≐_ : (x y : A) → Dec (x ≡ y)

open hasDecEq {{...}} public

{-# DISPLAY hasDecEq._≐_ x y = x ≐ y #-}

pattern equ    = yes refl
pattern neq ¬p = no ¬p

dec-equ :
  {ℓ : Level}
  {A : Set ℓ}
  {{_ : hasDecEq A}}
  (x : A)
  → ----------------
  does (x ≐ x) ≡ true
dec-equ x = dec-true (x ≐ x) refl

dec-neq :
  {ℓ : Level}
  {A : Set ℓ}
  {{_ : hasDecEq A}}
  (x y : A)
  (_ : ¬ x ≡ y)
  → ------------------
  does (x ≐ y) ≡ false
dec-neq x y = dec-false (x ≐ y)

infix 4 _≠_
_≠_ : {l : Level}{A : Set l}{{_ : hasDecEq A}}(x x' : A) → Set
x ≠ x' = does (x ≐ x') ≡ false

symm≠ :
  {l : Level}
  {A : Set l}
  {{_ : hasDecEq A}}
  (x x' : A)
  → ----------------
  x ≠ x' → x' ≠ x
symm≠ x x' _ with  x ≐ x'
symm≠  _ _ p    | equ with () ← p
symm≠  _ _ refl | neq q = dec-neq _ _ (q ∘ symm)

¬≡→≠  :
  {ℓ : Level}
  {A : Set ℓ}
  {{_ : hasDecEq A}}
  {x y : A}
  → ----------------
  ¬ x ≡ y → x ≠ y
¬≡→≠ {x = x} {y} = dec-neq x y

¬≠ :
  {l : Level}
  {A : Set l}
  {{_ : hasDecEq A}}
  (x : A)
  → ----------------
  ¬ x ≠ x
¬≠ x ¬p rewrite dec-equ x with () ← ¬p

≠→¬≡ :
  {ℓ : Level}
  {A : Set ℓ}
  {{_ : hasDecEq A}}
  {x y : A}
  → ----------------
  x ≠ y → ¬ x ≡ y
≠→¬≡ p refl with () ← ¬≠ _ p

inj≠ :
  {ℓ : Level}
  {A B : Set ℓ}
  {{_ : hasDecEq A}}
  {{_ : hasDecEq B}}
  {f : A → B}
  (injf : injection f)
  {x x' : A}
  → -----------------
  x ≠ x' → f x ≠ f x'
inj≠ injf p = ¬≡→≠ λ q → ≠→¬≡ p (injf q)

ap≠ :
  {ℓ : Level}
  {A B : Set ℓ}
  {{_ : hasDecEq A}}
  {{_ : hasDecEq B}}
  {f : A → B}
  {x x' : A}
  → -----------------
  f x ≠ f x' → x ≠ x'
ap≠ p = ¬≡→≠ λ{refl → ≠→¬≡ p refl}

instance
  hasDecEq⊎ :
    {l : Level}
    {A B : Set l}
    {{_ : hasDecEq A}}
    {{_ : hasDecEq B}}
    → ----------------
    hasDecEq (A ⊎ B)
  _≐_ {{hasDecEq⊎}} (ι₁ x) (ι₁ x') with  x ≐ x'
  ... | equ   = yes refl
  ... | neq f = no λ{refl → f refl}
  _≐_ {{hasDecEq⊎}} (ι₁ _) (ι₂ _) = no λ()
  _≐_ {{hasDecEq⊎}} (ι₂ _) (ι₁ _) = no λ()
  _≐_ {{hasDecEq⊎}} (ι₂ y) (ι₂ y') with y ≐ y'
  ... | equ   = yes refl
  ... | neq f = no λ{refl → f refl}

----------------------------------------------------------------------
-- Natural number type
----------------------------------------------------------------------
infix 8 _+1
data ℕ : Set where
  zero : ℕ
  _+1  : (n : ℕ) → ℕ

{-# BUILTIN NATURAL ℕ #-}

pattern _+2 x = (x +1) +1

infix 4 _≡ᴮ_
_≡ᴮ_ : ℕ → ℕ → 𝔹
0     ≡ᴮ 0    = true
x +1  ≡ᴮ y +1 = x ≡ᴮ y
_     ≡ᴮ _    = false

{-# BUILTIN NATEQUALS _≡ᴮ_ #-}

-- Decidable equality
instance
  hasDecEqℕ : hasDecEq ℕ
  _≐_ {{hasDecEqℕ}} zero zero = yes refl
  _≐_ {{hasDecEqℕ}} zero (y +1) = no λ()
  _≐_ {{hasDecEqℕ}} (x +1) zero = no λ()
  _≐_ {{hasDecEqℕ}} (x +1) (y +1) with  x ≐ y
  ... | equ   = yes refl
  ... | neq f = no λ{refl → f refl}

-- Addition
infixl 6 _+_
_+_ : ℕ → ℕ → ℕ
x + 0      = x
x + (y +1) = (x + y) +1

{-# BUILTIN NATPLUS _+_ #-}

0+ : ∀{x} → 0 + x ≡ x
0+ {0   }                = refl
0+ {x +1} rewrite 0+ {x} = refl

+1+ : ∀{x y} → (x +1) + y ≡ (x + y) +1
+1+ {x} {0   }                    = refl
+1+ {x} {y +1} rewrite +1+ {x}{y} = refl

+comm : ∀{x y} → x + y ≡ y + x
+comm {x} {0   }                   = symm 0+
+comm {x} {y +1}
  rewrite +1+ {y}{x} | +comm{x}{y} = refl


+1≠ : ∀{x y} → x ≠ y → x +1 ≠ y +1
+1≠ {x} {y} p = dec-neq (x +1) (y +1) λ{refl → ¬≠ x p}

+≠ : ∀ {x y} z → x ≠ y → x + z ≠ y + z
+≠         0       p = p
+≠ {x} {y} (z +1)  p = +1≠ {x + z} {y + z} (+≠ z p)

≠+1 : ∀ x → x ≠ x +1
≠+1 0      = dec-neq 0 1 λ ()
≠+1 (x +1) = +1≠ {x} (≠+1 x)

-- Predecessor
pred : ℕ → ℕ
pred 0      = 0
pred (x +1) = x

-- Monus
infixl 6 _∸_
_∸_ : ℕ → ℕ → ℕ
x ∸ 0   = x
x ∸ (y +1) = (pred x) ∸ y

∸refl : ∀ x → x ∸ x ≡ 0
∸refl 0      = refl
∸refl (x +1) = ∸refl x

0∸ : ∀ x → 0 ∸ x ≡ 0
0∸ zero   = refl
0∸ (x +1) = 0∸ x

-- Order
infix 4 _<_ _≤_ _>_ _≥_
data _≤_ : ℕ → ℕ → Set where
  ≤refl : {x : ℕ} →   x ≤ x
  ≤+1   : {x y : ℕ} → x ≤ y → x ≤ y +1

data _<_ : ℕ → ℕ → Set where
  <+1 : {x y : ℕ} → x ≤ y → x < y +1

1≤+1 : ∀{x} → 1 ≤ x +1
1≤+1 {zero} = ≤refl
1≤+1 {x +1} = ≤+1 (1≤+1 {x})

≤+ : ∀{x y} z → x ≤ y → x ≤ y + z
≤+ 0      p = p
≤+ (z +1) p = ≤+1 (≤+ z p)

≤+' : ∀{x y z} → x ≤ y → x ≤ z + y
≤+' {y = y} {z} p rewrite +comm {z}{y} = ≤+ z p

_>_ : ℕ → ℕ → Set
x > y = y < x

_≥_ : ℕ → ℕ → Set
x ≥ y = y ≤ x

0≤ : ∀{x} → 0 ≤ x
0≤ {0}    = ≤refl
0≤ {x +1} = ≤+1 0≤

+1≤ : ∀{x y} → x ≤ y → x +1 ≤ y +1
+1≤ ≤refl      = ≤refl
+1≤ (≤+1 x≤y)  = ≤+1 (+1≤ x≤y)

+≤ : ∀{x y} z → x ≤ y → x + z ≤ y + z
+≤ 0 p      = p
+≤ (z +1) p = +1≤ (+≤ z p)

+1< : ∀{x y} → x < y → x +1 < y +1
+1< (<+1 p) = <+1 (+1≤ p)

≤trans :
  {x y z : ℕ}
  (_ : x ≤ y)
  (_ : y ≤ z)
  → ---------
  x ≤ z
≤trans x≤y ≤refl = x≤y
≤trans x≤y (≤+1 y≤z) = ≤+1 (≤trans x≤y y≤z)

≤< :
  {x y z : ℕ}
  (_ : x ≤ y)
  (_ : y < z)
  → ---------
  x < z
≤< p (<+1 q) = <+1 (≤trans p q)

<≤ :
  {x y z : ℕ}
  (_ : x < y)
  (_ : y ≤ z)
  → ---------
  x < z
<≤ (<+1 p) ≤refl   = <+1 p
<≤ (<+1 p) (≤+1 q) = <+1 (≤trans (≤+1 p) q)

<< :
  {x y z : ℕ}
  (_ : x < y)
  (_ : y < z)
  → ---------
  x < z
<< (<+1 p) (q) = ≤< (≤+1 p) q

¬x+1≤x : ∀{x} → ¬ x +1 ≤ x
¬x+1≤x (≤+1 p) = ¬x+1≤x (≤trans (≤+1 ≤refl) p)

¬<> : ∀{x y} → x < y → ¬ y < x
¬<> (<+1 p) (<+1 q) = ¬x+1≤x (≤trans (≤+1 ≤refl) (≤trans (+1≤ p) q))

trich : ∀{x y} → x ≤ y → ¬(y ≡ x) → x < y
trich ≤refl q with () ← q refl
trich (≤+1 p) _ = <+1 p

≤≠ : ∀{x y} → x ≤ y → x ≠ y → x +1 ≤ y
≤≠ {x} ≤refl q with () ← ¬≠ x q
≤≠ (≤+1 p) _ = +1≤ p

≤∨≥ : ∀ x y → (x ≤ y) ⊎ (y ≤ x)
≤∨≥ 0      _             = ι₁ 0≤
≤∨≥ (x +1) 0             = ι₂ 0≤
≤∨≥ (x +1) (y +1) with ≤∨≥ x y
...               | ι₁ p = ι₁ (+1≤ p)
...               | ι₂ p = ι₂ (+1≤ p)

trich' : ∀{x y} → ¬(y ≤ x) → x < y
trich' {x} {y} _ with ≤∨≥ x y
trich' {x} {y} _  | ι₁ _ with  x ≐ y
trich'         _  | ι₁ q | neq f = trich q λ{refl → f refl}
trich'         p  | ι₁ q | equ with () ← p q
trich'         p  | ι₂ q with () ← p q

≤-1 : ∀{x y} → x +1 ≤ y +1 → x ≤ y
≤-1 ≤refl   = ≤refl
≤-1 (≤+1 p) = ≤trans (≤+1 ≤refl) p

+1≤→< : ∀ x y → x +1 ≤ y → x < y
+1≤→< _ _ p = <≤ (<+1 ≤refl) p

<→+1≤ : ∀ x y → x < y → x +1 ≤ y
<→+1≤ _ _ (<+1 p) = +1≤ p

+1≤→≠ : ∀ x y → x +1 ≤ y → y ≠ x
+1≤→≠ x y p = dec-neq y x λ{refl → ¬x+1≤x p}

<→≠ : ∀ x y → x < y → y ≠ x
<→≠ x (y +1) (<+1 p) = dec-neq (y +1) x λ{refl → ¬x+1≤x p}

pred+1≤ : ∀ x → x ≤ (pred x) +1
pred+1≤ 0      = 0≤
pred+1≤ (_ +1) = ≤refl

∸≤ : ∀{x} y → x ≤ (x ∸ y) + y
∸≤     0      = ≤refl
∸≤ {x} (y +1) = ≤trans (pred+1≤ x) (+1≤ (∸≤ {pred x} y))

predadj : ∀{x y} → x +1 ≤ y → x ≤ pred y
predadj {y = y +1} = ≤-1

∸adj : ∀{x y z} → x + y ≤ z → x ≤ z ∸ y
∸adj {y = 0   } p = p
∸adj {y = y +1} p = ∸adj {y = y} (predadj p)

pred+1 : ∀{x} → 1 ≤ x → (pred x) +1 ≡ x
pred+1 {x +1} p = refl

∸≤' : ∀{x y} → y ≤ x → (x ∸ y) + y ≡ x
∸≤' {x} {zero} p = refl
∸≤' {x} {y +1} p =
  proof
    ((pred x ∸ y + y) +1)
  ≡[ ap _+1 (∸≤' (predadj p)) ]
     (pred x) +1
  ≡[ pred+1 (≤trans 1≤+1 p) ]
    x
  qed

¬x<x : ∀ x → ¬(x < x)
¬x<x _ (<+1 p) = ¬x+1≤x p


-- Maximum of two numbers
max : ℕ → ℕ → ℕ
max 0      y      = y
max (x +1) 0      = x +1
max (x +1) (y +1) = (max x y) +1

≤max₁ : ∀{x y} → x ≤ max x y
≤max₁ {0   } {0   } = ≤refl
≤max₁ {x +1} {0   } = ≤refl
≤max₁ {0   } {y +1} = 0≤
≤max₁ {x +1} {y +1} = +1≤ ≤max₁

≤max₂ : ∀{x y} → y ≤ max x y
≤max₂ {0   } {0   } = ≤refl
≤max₂ {0   } {y +1} = ≤refl
≤max₂ {x +1} {0   } = 0≤
≤max₂ {x +1} {y +1} = +1≤ ≤max₂

max≤ : ∀{x y} → x ≤ y → max x y ≡ y
max≤ {0   } {_   } _                      = refl
max≤ {x +1} {y +1} p rewrite max≤ (≤-1 p) = refl

max≥ : ∀{x y} → x ≥ y → max x y ≡ x
max≥ {0}    {0   } _                      = refl
max≥ {x +1} {0   } p                      = refl
max≥ {x +1} {y +1} p rewrite max≥ (≤-1 p) = refl

≤lub : ∀ x y z → x ≤ z → y ≤ z → max x y ≤ z
≤lub x y z p q with ≤∨≥ x y
... | ι₁ x≤y rewrite max≤ x≤y = q
... | ι₂ x≥y rewrite max≥ x≥y = p

-- < is well founded
wf< : wf.iswf _<_
wf< x = wf.acc (α x)
  where
  α : ∀ x y → y < x → wf.Acc _<_ y
  β : ∀ x y → y ≤ x → wf.Acc _<_ y
  α (x +1) y (<+1 p) = β x y p
  β 0      _ ≤refl   = wf.acc (λ{ _ ()})
  β (x +1) _ ≤refl   = wf.acc (λ{ y (<+1 p) → β _ y p})
  β (x +1) y (≤+1 p) = wf.acc (λ z q → α x z (<≤ q p))

----------------------------------------------------------------------
-- Finite enumerated sets
----------------------------------------------------------------------
data Fin : ℕ → Set where
  zero : ∀{n} → Fin (n +1)
  succ : ∀{n} → Fin n → Fin (n +1)

-- Maximum of finitely many numbers
Max : {n : ℕ} → (Fin n → ℕ) → ℕ
Max {0} f = 0
Max {n +1} f = max (f zero) (Max (f ∘ succ))

≤Max :
  {n : ℕ}
  (f : Fin n → ℕ)
  (k : Fin n)
  → -------------
  f k ≤ Max f
≤Max {n +1} f zero     = ≤max₁
≤Max {n +1} f (succ k) = ≤trans (≤Max (f ∘ succ) k) ≤max₂

----------------------------------------------------------------------
-- Arrays
----------------------------------------------------------------------
record Array {l : Level}(A : Set l) : Set l where
  constructor mkArray
  field
    length : ℕ
    index  : Fin length → A

open Array public

----------------------------------------------------------------------
-- Lists
----------------------------------------------------------------------
infixr 6 _::_
data List {l : Level} (A : Set l) : Set l where
  []  : List A
  _::_ : (x : A) (xs : List A) → List A

{-# BUILTIN LIST List #-}

----------------------------------------------------------------------
--  Finite sets represented by trees
----------------------------------------------------------------------
infix 1 [_]
infixr 6 _∪_
data Fset {l : Level}(A : Set l) : Set l where
  Ø   : Fset A
  [_] : A → Fset A
  _∪_ : Fset A → Fset A → Fset A

∪inj₂ :
  {l : Level}
  {A : Set l}
  {xs xs' ys ys' : Fset A}
  → -------------------------------
  (xs ∪ xs' ≡ ys ∪ ys') → xs' ≡ ys'
∪inj₂ refl = refl

-- Functorial action
Fset′ :
  {l : Level}
  {A B : Set l}
  (f : A → B)
  → -------------
  Fset A → Fset B
Fset′ f Ø          = Ø
Fset′ f [ x ]      = [ f x ]
Fset′ f (xs ∪ xs') = Fset′ f xs ∪ Fset′ f xs'

-- Membership
infix 4 _∈_
data _∈_
  {l : Level}
  {A : Set l}
  (x : A)
  : ------------
  Fset A → Set l
  where
  ∈[] : x ∈ [ x ]
  ∈∪₁ : ∀{xs xs'} → x ∈ xs  → x ∈ xs ∪ xs'
  ∈∪₂ : ∀{xs xs'} → x ∈ xs' → x ∈ xs ∪ xs'

Fset′∈ :
  {l : Level}
  {A B : Set l}
  {f : A → B}
  {x : A}
  {xs : Fset A}
  (_ : x ∈ xs)
  → --------------
  f x ∈ Fset′ f xs
Fset′∈ ∈[]     = ∈[]
Fset′∈ (∈∪₁ p) = ∈∪₁ (Fset′∈ p)
Fset′∈ (∈∪₂ p) = ∈∪₂ (Fset′∈ p)

-- Non-membership
module _ {l : Level}{A : Set l}{{α : hasDecEq A}} where
  infix 4 _∉_
  data _∉_ (x : A) : Fset A → Set l
    where
    instance
      ∉Ø  : x ∉ Ø
      ∉[] : ∀{x'}{{p : x ≠ x'}} → x ∉ [ x' ]
      ∉∪  : ∀{xs xs'}{{p : x ∉ xs}}{{q : x ∉ xs'}} → x ∉ xs ∪ xs'

  ∉∪₁ :
    {x : A}
    {xs xs' : Fset A}
    → -------------------
    x ∉ xs ∪ xs' → x ∉ xs
  ∉∪₁ ∉∪ = it

  ∉∪₂ :
    {x : A}
    {xs xs' : Fset A}
    → --------------------
    x ∉ xs ∪ xs' → x ∉ xs'
  ∉∪₂ ∉∪ = it

  ∉[]₁ :
    {x x' : A}
    → -----------------
    x ∉ [ x' ] → x ≠ x'
  ∉[]₁ ∉[] = it

  ¬∈→∉ :
    {x : A}
    {xs : Fset A}
    → ----------------
    ¬(x ∈ xs) → x ∉ xs
  ¬∈→∉ {xs = Ø}     _ = ∉Ø
  ¬∈→∉ {xs = [ x' ]} p =
    ∉[] {x' = x'} {{¬≡→≠{{α}} λ{refl → p ∈[]}}}
  ¬∈→∉ {xs = xs ∪ xs'} p =
    ∉∪ {xs = xs} {xs' = xs'}
    {{¬∈→∉ λ q → p (∈∪₁ q)}}
    {{¬∈→∉ λ q → p (∈∪₂ q)}}

  ∉→¬∈ :
    {x : A}
    {xs : Fset A}
    {{p : x ∉ xs}}
    → ------------
    ¬ (x ∈ xs)
  ∉→¬∈ {x = x} {{p = ∉[]}} ∈[] with () ← ¬≠ x it
  ∉→¬∈ {{p = ∉∪}} (∈∪₁ q) = ∉→¬∈ q
  ∉→¬∈ {{p = ∉∪}} (∈∪₂ q) = ∉→¬∈ q

Fset′∉ :
  {l : Level}
  {A B : Set l}
  {{_ : hasDecEq A}}
  {{_ : hasDecEq B}}
  {f : A → B}
  {x : A}
  {xs : Fset A}
  {{p : f x ∉ Fset′ f xs}}
  → ----------------------
  x ∉ xs
Fset′∉ = ¬∈→∉ λ q → ∉→¬∈ (Fset′∈ q)

-- Finite union of finite subsets
⋃ : {l : Level}{A : Set l}{n : ℕ} → (Fin n → Fset A) → Fset A
⋃ {n = 0} _ = Ø
⋃ {n = n +1} f = f zero ∪ ⋃ {n = n} (f ∘ succ)

∉⋃ :
  {l : Level}
  {A : Set l}
  {{_ : hasDecEq A}}
  {n : ℕ}
  (f : Fin n → Fset A)
  {x : A}
  (k : Fin n)
  {{p : x ∉ ⋃ f}}
  → ------------------
  x ∉ f k
∉⋃ {n = n +1} f zero     {{p}} = ∉∪₁ p
∉⋃ {n = n +1} f (succ k) {{p}} = ∉⋃ {n = n} (f ∘ succ) k {{∉∪₂ p}}

∉⋃′ :
  {l : Level}
  {A : Set l}
  {{_ : hasDecEq A}}
  {n : ℕ}
  (f : Fin n → Fset A)
  {x : A}
  (g : (k : Fin n)→ x ∉ f k)
  → ------------------------
  x ∉ ⋃ f
∉⋃′ {n = 0}    _ _ = ∉Ø
∉⋃′ {n = n +1} f g =
  ∉∪{{p = g zero}}{{∉⋃′{n = n} (f ∘ succ) (g ∘ succ)}}

-- Subtract an element
infix 6 _-[_]
_-[_] :
  {l : Level}
  {A : Set l}
  {{α : hasDecEq A}}
  (xs : Fset A)
  (x : A)
  → ----------------
  Fset A
Ø         -[ x ] = Ø
[ y ]     -[ x ] = if does(x ≐ y) then Ø else [ y ]
(ys ∪ zs) -[ x ] = (ys -[ x ]) ∪ (zs -[ x ])

x∉xs-[x] :
  {l : Level}
  {A : Set l}
  {{α : hasDecEq A}}
  (xs : Fset A)
  {x : A}
  → ----------------
  x ∉ xs -[ x ]
x∉xs-[x] Ø = ∉Ø
x∉xs-[x] [ y ] {x} with x ≐ y
... | neq f        = ∉[]{{p = ¬≡→≠ f}}
... | equ          = ∉Ø
x∉xs-[x] (ys ∪ zs) = ∉∪{{p = x∉xs-[x] ys}}{{x∉xs-[x] zs}}

y∉zs→y∉zs-[x] :
  {l : Level}
  {A : Set l}
  {{α : hasDecEq A}}
  {x y : A}
  (zs : Fset A)
  → --------------------
  y ∉ zs → y ∉ zs -[ x ]
y∉zs→y∉zs-[x] Ø ∉Ø = ∉Ø
y∉zs→y∉zs-[x] {x = x} {y} [ z ] ∉[] with x ≐ z
... | equ                   = ∉Ø
... | neq f                 = ∉[]
y∉zs→y∉zs-[x] (zs ∪ zs') ∉∪ =
  ∉∪{{p = y∉zs→y∉zs-[x] zs it}}{{y∉zs→y∉zs-[x] zs' it}}

∉-[] :
  {l : Level}
  {A : Set l}
  {{α : hasDecEq A}}
  {xs : Fset A}
  {x y : A}
  (_ : y ∉ xs -[ x ])
  (_ : y ≠ x)
  → -----------------
  y ∉ xs
∉-[] {xs = Ø      } ∉Ø _              = ∉Ø
∉-[] {xs = [ z ]  } {x} p   q with x ≐ z
∉-[] {xs = [ _ ]  }     ∉[] _ | neq _ = ∉[]
∉-[] {xs = [ _ ]  }     _   q | equ   = ∉[]{{p = q}}
∉-[] {xs = ys ∪ zs}     ∉∪  q         =
  ∉∪{{p = ∉-[] it q}}{{∉-[] it q}}

-- Intersection
ι₂⁻¹ :
  {l : Level}
  {A B : Set l}
  → ------------------
  Fset(A ⊎ B) → Fset B
ι₂⁻¹ Ø         = Ø
ι₂⁻¹ [ ι₁ _ ]  = Ø
ι₂⁻¹ [ ι₂ y ]  = [ y ]
ι₂⁻¹ (xs ∪ ys) = ι₂⁻¹ xs ∪ ι₂⁻¹ ys

∉ι₂⁻¹→ι₂∉ :
  {l : Level}
  {A B : Set l}
  {{_ : hasDecEq A}}
  {{_ : hasDecEq B}}
  (zs : Fset(A ⊎ B))
  (y : B)
  → ---------------------
  y ∉ ι₂⁻¹ zs → ι₂ y ∉ zs
∉ι₂⁻¹→ι₂∉ Ø _ _ = ∉Ø
∉ι₂⁻¹→ι₂∉ [ ι₁ x ] y ∉Ø = ¬∈→∉ λ{()}
∉ι₂⁻¹→ι₂∉ {A = A} {B} [ ι₂ y' ] y (∉[]{{p = p}}) =
  ∉[]{{p = inj≠ {f = ι₂ {A = A}{B}}(injectionι₂) p}}
∉ι₂⁻¹→ι₂∉ (zs ∪ zs') y ∉∪ =
  ∉∪ {{p = ∉ι₂⁻¹→ι₂∉ zs y it}}{{∉ι₂⁻¹→ι₂∉ zs' y it}}

-- Maximum of a finite set of numbers
maxfs : Fset ℕ → ℕ
maxfs Ø         = 0
maxfs [ x ]     = x
maxfs (xs ∪ ys) = max (maxfs xs) (maxfs ys)

≤maxfs : ∀{xs x} → x ∈ xs → x ≤ maxfs xs
≤maxfs ∈[] = ≤refl
≤maxfs (∈∪₁ p) = ≤trans (≤maxfs p) ≤max₁
≤maxfs (∈∪₂ p) = ≤trans (≤maxfs p) ≤max₂

maxfs+1∉ : ∀ xs → (maxfs xs +1) ∉ xs
maxfs+1∉ xs =
  ¬∈→∉ λ p → wf.irrefl _<_ wf< (maxfs xs +1) (<+1 (≤maxfs p))

-- Finite ordinals
ordinal : ℕ → Fset ℕ
ordinal 0      = Ø
ordinal (n +1) = ordinal n ∪ [ n ]

∉ordinal→≥ : ∀ m n → m ∉ ordinal n → m ≥ n
∉ordinal→≥ _ 0 _ = 0≤
∉ordinal→≥ m (n +1) (∉∪{{q = ∉[]}}) =
  <→+1≤ n m (trich (∉ordinal→≥ m n it) (≠→¬≡ it))

----------------------------------------------------------------------
-- Dependent product
----------------------------------------------------------------------
infixr 6 _,_
record ∑ {l m : Level}(A : Set l)(B : A → Set m) : Set(l ⊔ m) where
  constructor _,_
  field
    π₁ : A
    π₂ : B π₁

{-# BUILTIN SIGMA ∑ #-}

open ∑ public

infix 2 ∑-syntax
∑-syntax : {l m : Level}(A : Set l) → (A → Set m) → Set (l ⊔ m)
∑-syntax = ∑
syntax ∑-syntax A (λ x → B) = ∑ x ∶ A , B

pair :
  {l m : Level}
  {A : Set l}
  (B : A → Set m)
  (x : A)
  (_ : B x)
  → -------------
  ∑ A B
pair _ x y = (x , y)

----------------------------------------------------------------------
-- Cartesian product
----------------------------------------------------------------------
infixr 7 _×_
_×_ : {l m : Level} → Set l → Set m → Set (l ⊔ m)
A × B = ∑ A (λ _ → B)

-- Iterated cartesian product
infixr 6 _^_
_^_ : {l : Level} → Set l → ℕ → Set l
A ^ 0     = 𝟙
A ^(n +1) = A × (A ^ n)
