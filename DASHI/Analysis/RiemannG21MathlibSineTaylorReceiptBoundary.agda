module DASHI.Analysis.RiemannG21MathlibSineTaylorReceiptBoundary where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- External machine-checked source inventory for the fifth-order sine
-- remainder needed by the odd determinant Taylor budget.
--
-- Mathlib owns:
--
--   Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
--     Real.hasSum_sin
--     Real.sin_eq_tsum
--
--   Mathlib.Analysis.Calculus.Taylor
--     taylor_mean_remainder_lagrange_iteratedDeriv
--     exists_taylor_mean_remainder_bound
--
-- The intended specialization is
--
--   |sin x - x + x^3/6| <= |x|^5/120,
--
-- using the uniform bound |sin^(5)|<=1 (equivalently a sin/cos derivative
-- cycle plus |sin|,|cos|<=1).  This file records theorem ownership and the
-- exact specialization target.  It does not count the specialized Lean proof
-- as present until a proof term is actually supplied in an approved Lean
-- owner or transported into Agda.
------------------------------------------------------------------------

record MathlibSineTaylorReceipt : Set where
  constructor mathlibSineTaylorReceipt
  field
    mathlibSeriesModule : String
    realHasSumSin : String
    realSinEqTsum : String
    mathlibTaylorModule : String
    lagrangeIteratedDerivTheorem : String
    remainderBoundTheorem : String
    specializedTarget : String
    boundedDerivativeRequirement : String

canonicalMathlibSineTaylorReceipt : MathlibSineTaylorReceipt
canonicalMathlibSineTaylorReceipt =
  mathlibSineTaylorReceipt
    "Mathlib.Analysis.SpecialFunctions.Trigonometric.Series"
    "Real.hasSum_sin"
    "Real.sin_eq_tsum"
    "Mathlib.Analysis.Calculus.Taylor"
    "taylor_mean_remainder_lagrange_iteratedDeriv"
    "exists_taylor_mean_remainder_bound"
    "|sin x - x + x^3/6| <= |x|^5/120"
    "Bound the fifth derivative of sin in norm by 1 on the segment between 0 and x."

record MathlibSineTaylorBoundary : Set where
  constructor mathlibSineTaylorBoundary
  field
    sinePowerSeriesLocated : Bool
    sinePowerSeriesLocatedIsTrue : sinePowerSeriesLocated ≡ true
    generalTaylorRemainderLocated : Bool
    generalTaylorRemainderLocatedIsTrue : generalTaylorRemainderLocated ≡ true
    specializedFifthOrderProofTermPresent : Bool
    specializedFifthOrderProofTermPresentIsFalse :
      specializedFifthOrderProofTermPresent ≡ false
    specializedFifthOrderBoundDerivedInAgda : Bool
    specializedFifthOrderBoundDerivedInAgdaIsFalse :
      specializedFifthOrderBoundDerivedInAgda ≡ false

canonicalMathlibSineTaylorBoundary : MathlibSineTaylorBoundary
canonicalMathlibSineTaylorBoundary =
  mathlibSineTaylorBoundary true refl true refl false refl false refl
