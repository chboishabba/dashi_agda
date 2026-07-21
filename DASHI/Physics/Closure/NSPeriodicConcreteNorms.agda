module DASHI.Physics.Closure.NSPeriodicConcreteNorms where

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _*_; _+_)

------------------------------------------------------------------------
-- Exact candidate constants used by the deterministic finite program.
--
-- These constants belong to the frozen finite normalization.  Identifying each
-- one with the corresponding theorem on the official periodic carrier remains a
-- proof obligation; the status booleans below therefore stay false.
------------------------------------------------------------------------

record ConcreteTailConstants : Set where
  field
    twoPlacements : Nat
    bonyConstant : Nat
    bernsteinShellConstant : Nat
    lerayConstant : Nat
    fourierNormalizationConstant : Nat

open ConcreteTailConstants public

periodicTailConstants : ConcreteTailConstants
periodicTailConstants = record
  { twoPlacements = 2
  ; bonyConstant = 2
  ; bernsteinShellConstant = 2
  ; lerayConstant = 1
  ; fourierNormalizationConstant = 1
  }

farHighConstantProduct : Nat
farHighConstantProduct =
  twoPlacements periodicTailConstants
  * bonyConstant periodicTailConstants
  * bernsteinShellConstant periodicTailConstants
  * lerayConstant periodicTailConstants
  * fourierNormalizationConstant periodicTailConstants

farHighConstantProductIsEight : farHighConstantProduct ≡ 8
farHighConstantProductIsEight = refl

-- 8 * (1/128) = 1/16 in the selected finite model.
farHighR8ReducedNumerator farHighR8ReducedDenominator : Nat
farHighR8ReducedNumerator = 1
farHighR8ReducedDenominator = 16

farHighR8DenominatorIsSixteen : farHighR8ReducedDenominator ≡ 16
farHighR8DenominatorIsSixteen = refl

nearLowHighConstant nearHighLowConstant nearHighHighConstant : Nat
nearLowHighConstant = 2
nearHighLowConstant = 2
nearHighHighConstant = 4

nearDeltaDenominator : Nat
nearDeltaDenominator = 16

nearLowHighDeltaNumerator nearHighLowDeltaNumerator nearHighHighDeltaNumerator : Nat
nearLowHighDeltaNumerator = 1
nearHighLowDeltaNumerator = 1
nearHighHighDeltaNumerator = 2

nearDeltaNumeratorsSumToQuarter :
  nearLowHighDeltaNumerator
    + nearHighLowDeltaNumerator
    + nearHighHighDeltaNumerator
  ≡ 4
nearDeltaNumeratorsSumToQuarter = refl

optimizedNearResidualCoefficient : Nat
optimizedNearResidualCoefficient = 64

candidateConstantsAreOfficialCarrierTheorems : Bool
candidateConstantsAreOfficialCarrierTheorems = false
