module DASHI.MDL.MDLDescent where

open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational using (_≤_)

open import DASHI.Core.Q using (ℚ)

record MDLStructure (X : Set) : Set₁ where
  field
    MDL : X → ℚ

record MDLDescent (X : Set) (T : X → X) (MS : MDLStructure X) : Set where
  field
    descent : ∀ x → _≤_ (MDLStructure.MDL MS (T x)) (MDLStructure.MDL MS x)
