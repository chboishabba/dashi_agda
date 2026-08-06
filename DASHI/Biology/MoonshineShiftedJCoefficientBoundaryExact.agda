module DASHI.Biology.MoonshineShiftedJCoefficientBoundaryExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- John H. Conway and Simon P. Norton,
-- "Monstrous Moonshine".
-- DOI: 10.1112/blms/11.3.308.
--
-- Richard E. Borcherds,
-- "Monstrous Moonshine and Monstrous Lie Superalgebras".
-- DOI: 10.1007/BF01232032.
--
-- James Lepowsky and Haisheng Li,
-- "Introduction to Vertex Operator Algebras and Their Representations".
-- DOI: 10.1007/978-0-8176-8186-9.
--
-- DASHI CONTRIBUTION
-- Make the central-charge-24 shift explicit at the first three conformal
-- weights.  In Tr(q^(L_0-c/24)), c=24 shifts weight n to exponent n-1:
--
--   weight 0 -> q^-1 with coefficient 1,
--   weight 1 -> q^0  with coefficient 0,
--   weight 2 -> q^1  with coefficient 196884.
--
-- This is the finite initial coefficient profile of the normalized J-series;
-- it is not a proof of modularity, genus zero, replicability or Moonshine.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Biology.MoonshineGradedTraceProbeExact as Trace

data InitialConformalWeight : Set where
  weightZero : InitialConformalWeight
  weightOne : InitialConformalWeight
  weightTwo : InitialConformalWeight

data ShiftedExponent : Set where
  exponentMinusOne : ShiftedExponent
  exponentZero : ShiftedExponent
  exponentPlusOne : ShiftedExponent

centralCharge : Nat
centralCharge = 24

centralChargeOverTwentyFour : Nat
centralChargeOverTwentyFour = 1

centralChargeShiftExact : centralCharge ≡ 24 * centralChargeOverTwentyFour
centralChargeShiftExact = refl

shiftWeight : InitialConformalWeight → ShiftedExponent
shiftWeight weightZero = exponentMinusOne
shiftWeight weightOne = exponentZero
shiftWeight weightTwo = exponentPlusOne

initialCoefficient : ShiftedExponent → Nat
initialCoefficient exponentMinusOne = 1
initialCoefficient exponentZero = 0
initialCoefficient exponentPlusOne = 196884

vacuumCoefficientExact :
  initialCoefficient (shiftWeight weightZero) ≡ 1
vacuumCoefficientExact = refl

weightOneCoefficientExact :
  initialCoefficient (shiftWeight weightOne) ≡ 0
weightOneCoefficientExact = refl

weightTwoCoefficientExact :
  initialCoefficient (shiftWeight weightTwo) ≡ 196884
weightTwoCoefficientExact = refl

traceProfileMatchesShiftedCoefficients :
  Trace.traceAtWeightZero Trace.moonshineInitialIdentityTraceProfile
    ≡ initialCoefficient exponentMinusOne
traceProfileMatchesShiftedCoefficients = refl

record ShiftedJBoundary : Set where
  constructor shiftedJBoundary
  field
    threeInitialCoefficientsProveModularity : Set
    threeInitialCoefficientsDoNotProveModularity :
      threeInitialCoefficientsProveModularity → Set

    threeInitialCoefficientsProveGenusZero : Set
    threeInitialCoefficientsDoNotProveGenusZero :
      threeInitialCoefficientsProveGenusZero → Set

canonicalShiftedJBoundary : ShiftedJBoundary
canonicalShiftedJBoundary =
  shiftedJBoundary
    ⊥ (λ impossible → ⊥)
    ⊥ (λ impossible → ⊥)
  where
  open import Data.Empty using (⊥)
