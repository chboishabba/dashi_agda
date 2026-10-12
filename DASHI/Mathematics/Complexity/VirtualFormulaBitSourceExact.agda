module DASHI.Mathematics.Complexity.VirtualFormulaBitSourceExact where

------------------------------------------------------------------------
-- RESOURCE-ACCOUNTED VIRTUAL BOOLEAN-FORMULA INPUT
--
-- Literal self-quotation is impossible at positive Cook budget in the current
-- single-tape architecture because the full bitstring must be written before D
-- starts.  The replacement substrate is indexed access:
--
--   compact description -> requested bit of encodeFormulaBits(formula)
--
-- A consumer may ask for bits on demand; no field grants the full encoded list
-- for free.  Query work is explicit and polynomially bounded in the formula's
-- encoded length plus the requested index.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Maybe using (Maybe; nothing; just)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Data.Nat.Base using (_≤_)

import DASHI.Mathematics.Complexity.CookLevinCircuitGCTBoundary as Cook
import DASHI.Mathematics.Complexity.PNotEqualsNPCookFormulaBinaryCodecExact as Binary
import DASHI.Mathematics.Complexity.PolynomialClockArithmeticExact as Clock

------------------------------------------------------------------------
-- Position-indexed list semantics, independent of any lookup implementation.
------------------------------------------------------------------------

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
bitAtFunctional bitHere bitHere =
  Agda.Builtin.Equality.refl
bitAtFunctional (bitThere left) (bitThere right) =
  bitAtFunctional left right

------------------------------------------------------------------------
-- Shared polynomial shape for one virtual read.
------------------------------------------------------------------------

queryPolynomialBudget :
  Nat → Nat → Cook.BooleanFormula → Nat → Nat
queryPolynomialBudget coefficient degree formula index =
  coefficient
  * Clock.natPower
      (suc (Binary.formulaBitCodeLength formula + index))
      degree

------------------------------------------------------------------------
-- Virtual source contract.
------------------------------------------------------------------------

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

------------------------------------------------------------------------
-- A description-bearing variant: this is the actual self-quotation target.
-- The description is what a finite prefix may materialise; the formula itself
-- remains the extensional specification used only in the correctness theorem.
------------------------------------------------------------------------

record DescribedVirtualFormulaBitSource
    (formula : Cook.BooleanFormula) : Set₂ where
  field
    Description : Set
    description : Description
    descriptionSize : Description → Nat

    source : VirtualFormulaBitSource formula

    -- No claim that descriptionSize bounds the full formula code.  The intended
    -- use is the opposite: a compact description such as machine/input/T from
    -- which requested Cook bits are generated on demand.

open DescribedVirtualFormulaBitSource public

------------------------------------------------------------------------
-- TRUST BOUNDARY
--
-- This owner does not assert that the existing Cook constructor has such an
-- indexed generator, nor that a standard TM can consume it with polynomial
-- overhead.  Those are now the two explicit constructive obligations.
------------------------------------------------------------------------
