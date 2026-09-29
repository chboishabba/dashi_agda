{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119AntigravitySU2TraceThresholdSameObjectExact where

open import Agda.Builtin.Equality using (_≡_; refl; cong)
open import Relation.Binary.PropositionalEquality using (subst)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using (ℚ; _*_)
import Data.Rational.Tactic.RingSolver as ℚRing

import Real as Bishop
import RealProperties as BishopP

import DASHI.Physics.Foundations.CMP119AntigravityBishopInversePiSquaredUnitBoundExact as Pi
import DASHI.Physics.Foundations.CMP119AntigravityCanonicalBishopSU2ConventionExact as Trace
import DASHI.Physics.Foundations.CMP119AntigravityPhysicalSU2ThresholdBelowHistoryExact as Threshold
import DASHI.Physics.YangMills.BalabanClayT4BishopFourCornerIntervalExact as Embed
open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- SAME-OBJECT FACTOR-OF-TWO NORMALIZATION
--
-- Trace coefficient magnitude:
--
--   kappa = (11/48) pi^{-2}.
--
-- Active-stress no-go threshold:
--
--   2 kappa = (11/24) pi^{-2}.
--
-- Both use the exact same Bishop/Machin pi^{-2}; this module proves the
-- factor-of-two identity rather than treating the threshold as a parallel
-- independently normalized constant.
------------------------------------------------------------------------

two : ℚ
two = + 2 / 1

traceMagnitude : Bishop.ℝ
traceMagnitude =
  Bishop._*_
    (Embed.embed Trace.elevenFortyEight)
    Pi.inversePiSquared

twoTimesTraceMagnitude : Bishop.ℝ
twoTimesTraceMagnitude =
  Bishop._*_ (Embed.embed two) traceMagnitude

rationalCoefficientDouble :
  two * Trace.elevenFortyEight
  ≡ Threshold.elevenTwentyFour
rationalCoefficientDouble = ℚRing.solve []

embeddedCoefficientDouble :
  Bishop._≃_
    (Bishop._*_
      (Embed.embed two)
      (Embed.embed Trace.elevenFortyEight))
    (Embed.embed Threshold.elevenTwentyFour)
embeddedCoefficientDouble =
  BishopP.≃-trans
    (BishopP.≃-symm
      (Embed.embedMul two Trace.elevenFortyEight))
    (subst
      (λ value →
        Bishop._≃_
          (Embed.embed value)
          (Embed.embed Threshold.elevenTwentyFour))
      rationalCoefficientDouble
      BishopP.≃-refl)

physicalThresholdIsTwiceTraceMagnitude :
  Bishop._≃_
    twoTimesTraceMagnitude
    Threshold.physicalSU2NoGoThreshold
physicalThresholdIsTwiceTraceMagnitude =
  let open BishopP.ℝ-Solver
  in
  BishopP.≃-trans
    (solve 3
      (λ twoCoeff traceCoeff pi2 →
        twoCoeff ⊗ (traceCoeff ⊗ pi2)
        ⊜ (twoCoeff ⊗ traceCoeff) ⊗ pi2)
      BishopP.≃-refl
      (Embed.embed two)
      (Embed.embed Trace.elevenFortyEight)
      Pi.inversePiSquared)
    (BishopP.*-congʳ
      embeddedCoefficientDouble)

traceCoefficientIsNegativeMagnitude :
  Bishop._≃_
    Trace.bishopSU2TraceCoefficient
    (Bishop.- traceMagnitude)
traceCoefficientIsNegativeMagnitude = BishopP.≃-refl

su2TraceThresholdSameObjectLevel : ProofLevel
su2TraceThresholdSameObjectLevel = machineChecked
