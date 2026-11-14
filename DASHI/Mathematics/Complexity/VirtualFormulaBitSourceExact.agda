module DASHI.Mathematics.Complexity.VirtualFormulaBitSourceExact where

------------------------------------------------------------------------
-- RESOURCE-ACCOUNTED VIRTUAL BOOLEAN-FORMULA INPUT
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; _∷_)
open import Agda.Builtin.Maybe using (Maybe; just)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Data.Nat.Base using (_≤_)

import DASHI.Mathematics.Complexity.CookLevinCircuitGCTBoundary as Cook
import DASHI.Mathematics.Complexity.PNotEqualsNPCookFormulaBinaryCodecExact as Binary
import DASHI.Mathematics.Complexity.PolynomialClockArithmeticExact as Clock

data BitAt : Nat → List Bool → Bool → Set where
  bitHere :
    ∀ {bit rest} →
    BitAt zero (bit ∷ rest) bit

  bitThere :
    ∀ {index head rest bit} →
    BitAt index rest bit →
    BitAt (suc index) (head ∷ rest) bit

bitAtFunctional :
  ∀ {index bits left right} →
  BitAt index bits left →
  BitAt index bits right →
  left ≡ right
bitAtFunctional bitHere bitHere = refl
bitAtFunctional (bitThere left) (bitThere right) =
  bitAtFunctional left right

queryPolynomialBudget :
  Nat → Nat → Cook.BooleanFormula → Nat → Nat
queryPolynomialBudget coefficient degree formula index =
  coefficient
  * Clock.natPower
      (suc (Binary.formulaBitCodeLength formula + index))
      degree

record VirtualFormulaBitSource
    (formula : Cook.BooleanFormula) : Set₁ where
  field
    readBit : Nat → Maybe Bool

    readSound :
      ∀ {index bit} →
      readBit index ≡ just bit →
      BitAt index (Binary.encodeFormulaBits formula) bit

    readComplete :
      ∀ {index bit} →
      BitAt index (Binary.encodeFormulaBits formula) bit →
      readBit index ≡ just bit

    queryWork : Nat → Nat
    queryCoefficient : Nat
    queryDegree : Nat

    queryWorkPolynomial :
      (index : Nat) →
      queryWork index
      ≤ queryPolynomialBudget
          queryCoefficient queryDegree formula index

open VirtualFormulaBitSource public

record DescribedVirtualFormulaBitSource
    (formula : Cook.BooleanFormula) : Set₂ where
  field
    Description : Set
    description : Description
    descriptionSize : Description → Nat
    source : VirtualFormulaBitSource formula

open DescribedVirtualFormulaBitSource public

------------------------------------------------------------------------
-- TRUST BOUNDARY
--
-- No full encoded list is supplied by this interface. The remaining producers
-- are an indexed generator for the ACTUAL guarded Cook constructor and a
-- standard-machine simulation that consumes those reads with charged overhead.
------------------------------------------------------------------------
