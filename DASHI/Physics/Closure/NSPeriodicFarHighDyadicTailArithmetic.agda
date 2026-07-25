module DASHI.Physics.Closure.NSPeriodicFarHighDyadicTailArithmetic where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _*_; pred)

open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Exact denominator arithmetic for the surplus-one geometric tail.
--
-- sum_{n >= R} 2^{-n} = 2^{-(R-1)} for R > 0.  This module does
-- not assert the analytic series identity; it gives its exact finite arithmetic
-- target, including the already selected structural constant eight.
------------------------------------------------------------------------

powTwo : Nat → Nat
powTwo zero = 1
powTwo (suc n) = 2 * powTwo n

surplusOneTailDenominator : Nat → Nat
surplusOneTailDenominator radius = powTwo (pred radius)

radiusEightOnePlacementDenominator :
  surplusOneTailDenominator 8 ≡ 128
radiusEightOnePlacementDenominator = refl

selectedStructuralConstant : Nat
selectedStructuralConstant = 8

canonicalSixteenthDenominator : Nat
canonicalSixteenthDenominator = 16

-- Cross-multiplication certificate for 8 * (1/128) = 1/16.
radiusEightStructuralReduction :
  selectedStructuralConstant * canonicalSixteenthDenominator ≡ 128
radiusEightStructuralReduction = refl

record RadiusEightDyadicTailCertificate : Set where
  field
    one-placement-denominator : surplusOneTailDenominator 8 ≡ 128
    structural-reduction :
      selectedStructuralConstant * canonicalSixteenthDenominator ≡ 128

radiusEightDyadicTailCertificate : RadiusEightDyadicTailCertificate
radiusEightDyadicTailCertificate = record
  { one-placement-denominator = radiusEightOnePlacementDenominator
  ; structural-reduction = radiusEightStructuralReduction
  }

farHighDyadicTailArithmeticLevel : ProofLevel
farHighDyadicTailArithmeticLevel = machineChecked
