module Everything where

{-
   An Agda developement for some of the material in the paper:

   Andrew M. Pitts, LOCALLY NAMELESS SETS

   Checked with Agda v2.6.2.2

   © 2023 Andrew M Pitts
   Creative Commons License CC-BY
-}

-- Some preliminary definitions and lemmas
open import Prelude

-- Postulated functional extensionalty
open import FunExt

-- Section 2.1
open import Unfinite

-- Section 2.2
open import oc-Sets

-- Section 2.3
open import Freshness

-- section 2.4
open import LocalClosedness

-- Section 2.5
open import Support

-- Section2.6
open import AbstractionConcretion

-- Section 2.7
open import RenamingRendexingSwapping

-- Section 3.1
open import Category

-- Sections 3.2 and 3.3
open import fsRenset
open import FullTransformationSemigroup

-- Section 3.4
open import Shift

-- Section 4
open import BindingSignature
open import LambdaTerms
