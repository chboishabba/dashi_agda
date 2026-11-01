{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119AntigravityCanonicalBishopSU2ConventionExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base as ℚ using (ℚ)
open import Data.Integer.Base using (+_)

import Real as Bishop

import DASHI.Physics.Foundations.CMP119AntigravityBishopInversePiSquaredUnitBoundExact as Pi
import DASHI.Physics.YangMills.BalabanClayP3PhysicalOneStepTransferExact as P3
import DASHI.Physics.YangMills.BalabanClayT4RunningCouplingConventionBridgeExact as Running
import DASHI.Physics.YangMills.BalabanClayT4BetaNormalizationConventionExact as Beta
import DASHI.Physics.YangMills.BalabanClayT4BishopFourCornerIntervalExact as Embed
import DASHI.Physics.YangMills.BalabanYM4SU2GaussianBetaLowerExact as SU2
open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- SAME-OBJECT S4b CONSTRUCTOR
--
-- The abstract running-coupling convention leaves inversePiSquared free.
-- This preferred SU(2) Bishop-real constructor removes that freedom:
--
--   Scalar            = Bishop real
--   C_A               = 2
--   rational embedding= canonical Bishop rational embedding
--   multiplication    = Bishop multiplication
--   inversePiSquared  = inverse(bishopMachinPi)^2
--
-- Therefore every consumer of this constructor uses the SAME pi^{-2} object
-- as the physical anomaly threshold theorem.
------------------------------------------------------------------------

record CanonicalBishopSU2RunningInputs (Scale : Set) : Set₁ where
  field
    recursion : P3.RunningCouplingRecursion Scale Bishop.ℝ
    logBlocking : Scale → Bishop.ℝ

    betaLogBlockingDefinition : ∀ scale →
      P3.betaLogBlocking recursion scale
      ≡ Bishop._*_
          (Bishop._*_
            (Embed.embed
              (Beta.pureYMInverseCouplingCoefficient
                SU2.su2Casimir))
            Pi.inversePiSquared)
          (logBlocking scale)

open CanonicalBishopSU2RunningInputs public

canonicalBishopSU2RunningConvention :
  ∀ {Scale} →
  CanonicalBishopSU2RunningInputs Scale →
  Running.ConventionMatchedRunningCoupling Scale Bishop.ℝ
canonicalBishopSU2RunningConvention inputs = record
  { Running.ConventionMatchedRunningCoupling.recursion =
      recursion inputs
  ; Running.ConventionMatchedRunningCoupling.casimirAdjoint =
      SU2.su2Casimir
  ; Running.ConventionMatchedRunningCoupling.embedRational =
      Embed.embed
  ; Running.ConventionMatchedRunningCoupling.multiply =
      Bishop._*_
  ; Running.ConventionMatchedRunningCoupling.inversePiSquared =
      Pi.inversePiSquared
  ; Running.ConventionMatchedRunningCoupling.logBlocking =
      logBlocking inputs
  ; Running.ConventionMatchedRunningCoupling.betaLogBlockingDefinition =
      betaLogBlockingDefinition inputs
  }

canonicalRunningInversePiSquaredIsMachin :
  ∀ {Scale}
    (inputs : CanonicalBishopSU2RunningInputs Scale) →
  Running.inversePiSquared (canonicalBishopSU2RunningConvention inputs)
  ≡ Pi.inversePiSquared
canonicalRunningInversePiSquaredIsMachin inputs = refl

canonicalRunningCasimirIsSU2 :
  ∀ {Scale}
    (inputs : CanonicalBishopSU2RunningInputs Scale) →
  Running.casimirAdjoint (canonicalBishopSU2RunningConvention inputs)
  ≡ SU2.su2Casimir
canonicalRunningCasimirIsSU2 inputs = refl

------------------------------------------------------------------------
-- Lorentzian trace coefficient on the SAME Bishop scalar carrier.
------------------------------------------------------------------------

elevenFortyEight : ℚ
elevenFortyEight = + 11 / 48

bishopSU2TraceCoefficient : Bishop.ℝ
bishopSU2TraceCoefficient =
  Bishop.-_
    (Bishop._*_
      (Embed.embed elevenFortyEight)
      Pi.inversePiSquared)

record CanonicalBishopSU2TraceBoundary : Set₁ where
  field
    selectedLorentzianF2 : Bishop.ℝ
    selectedQuantumTrace : Bishop.ℝ

    selectedTraceDefinition :
      selectedQuantumTrace
      ≡ Bishop._*_ bishopSU2TraceCoefficient selectedLorentzianF2

open CanonicalBishopSU2TraceBoundary public

runningAndTraceShareInversePiSquared : Bool
runningAndTraceShareInversePiSquared = true

runningAndTraceShareInversePiSquaredIsTrue :
  runningAndTraceShareInversePiSquared ≡ true
runningAndTraceShareInversePiSquaredIsTrue = refl

separateInversePiSquaredIdentificationRequiredOnCanonicalRoute : Bool
separateInversePiSquaredIdentificationRequiredOnCanonicalRoute = false

separateInversePiSquaredIdentificationRequiredOnCanonicalRouteIsFalse :
  separateInversePiSquaredIdentificationRequiredOnCanonicalRoute ≡ false
separateInversePiSquaredIdentificationRequiredOnCanonicalRouteIsFalse = refl

canonicalBishopSU2ConventionLevel : ProofLevel
canonicalBishopSU2ConventionLevel = machineChecked

-- Remaining physical input is betaLogBlockingDefinition for the literal RG
-- recursion, not a choice of pi convention.
literalBishopSU2RunningCoefficientLevel : ProofLevel
literalBishopSU2RunningCoefficientLevel = conditional
