module FunExt where

open import Prelude

----------------------------------------------------------------------
-- Postulated function extensionality
----------------------------------------------------------------------
postulate
  funext :
    {l m : Level}
    {A : Set l}
    {B : A → Set m}
    {f g : (x : A) → B x}
    (_ : ∀ x → f x ≡ g x)
    → -------------------
    f ≡ g
