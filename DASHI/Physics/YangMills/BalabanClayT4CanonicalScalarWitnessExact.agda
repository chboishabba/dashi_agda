module DASHI.Physics.YangMills.BalabanClayT4CanonicalScalarWitnessExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Integer.Base using (+_)
open import Data.Rational using (ℚ; 0ℚ; 1ℚ; _+_; _*_; _<_; _/_; Positive)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanClayP4CommonParameterDomainExact
open import DASHI.Physics.YangMills.BalabanTraceKoteckyPreissGeometricExact using (half)

------------------------------------------------------------------------
-- T4/P4: an exact common scalar margin certificate.
--
-- This does not identify analytic constants with their Wilson-model values.
-- It removes the separate-constant loophole: once the physical estimates are
-- shown below the displayed owners, all P1--P5 scalar inequalities hold at one
-- and the same canonical tuple.
------------------------------------------------------------------------

record PositiveMargin (left right : ℚ) : Set where
  constructor margin
  field
    slack : ℚ
    slackPositive : 0ℚ < slack
    closes : left + slack ≡ right

open PositiveMargin public

positiveRational : ∀ numerator denominator →
  Positive (+ numerator / denominator) →
  0ℚ < (+ numerator / denominator)
positiveRational numerator denominator positive =
  ℚP.positive⁻¹ (+ numerator / denominator)

canonicalGreenUpper canonicalNonlinearSlope : ℚ
canonicalGreenUpper = + 16 / 1
canonicalNonlinearSlope = + 2 / 1

canonicalCriticalProduct : ℚ
canonicalCriticalProduct =
  canonicalGreenUpper * canonicalNonlinearSlope
    * backgroundRadius canonicalClayParameters

canonicalCriticalProductExact :
  canonicalCriticalProduct ≡ + 1 / 32
canonicalCriticalProductExact = ℚRing.solve-∀

canonicalContractionMargin :
  PositiveMargin canonicalCriticalProduct half
canonicalContractionMargin = margin (+ 15 / 32)
  (let
    instance
      positive : Positive (+ 15 / 32)
      positive = ℚP.normalize-pos 15 32
   in ℚP.positive⁻¹ (+ 15 / 32))
  (ℚRing.solve-∀)

canonicalBranchingRatio : ℚ
canonicalBranchingRatio = (+ 8 / 1) * (+ 1 / 16)

canonicalBranchingRatioExact : canonicalBranchingRatio ≡ half
canonicalBranchingRatioExact = ℚRing.solve-∀

canonicalKPMargin : PositiveMargin canonicalBranchingRatio 1ℚ
canonicalKPMargin = margin half
  (let
    instance
      positive : Positive half
      positive = ℚP.normalize-pos 1 2
   in ℚP.positive⁻¹ half)
  (ℚRing.solve-∀)

canonicalFiveTermLoss : ℚ
canonicalFiveTermLoss =
  (+ 1 / 1024) + ((+ 1 / 1024) + ((+ 1 / 1024)
    + ((+ 1 / 1024) + (+ 1 / 1024))))

canonicalOneStepLossBudget : ℚ
canonicalOneStepLossBudget = + 1 / 128

canonicalOneStepMargin :
  PositiveMargin canonicalFiveTermLoss canonicalOneStepLossBudget
canonicalOneStepMargin = margin (+ 3 / 1024)
  (let
    instance
      positive : Positive (+ 3 / 1024)
      positive = ℚP.normalize-pos 3 1024
   in ℚP.positive⁻¹ (+ 3 / 1024))
  (ℚRing.solve-∀)

canonicalQuarticRemainderCoefficient : ℚ
canonicalQuarticRemainderCoefficient = + 1 / 256

canonicalBetaRemainderMargin :
  PositiveMargin canonicalQuarticRemainderCoefficient
    canonicalOneStepLossBudget
canonicalBetaRemainderMargin = margin (+ 1 / 256)
  (let
    instance
      positive : Positive (+ 1 / 256)
      positive = ℚP.normalize-pos 1 256
   in ℚP.positive⁻¹ (+ 1 / 256))
  (ℚRing.solve-∀)

canonicalTerminalDimensionlessMass canonicalTransportDefect : ℚ
canonicalTerminalDimensionlessMass = half
canonicalTransportDefect = + 1 / 4

canonicalMassSurvivalMargin :
  PositiveMargin canonicalTransportDefect canonicalTerminalDimensionlessMass
canonicalMassSurvivalMargin = margin (+ 1 / 4)
  (let
    instance
      positive : Positive (+ 1 / 4)
      positive = ℚP.normalize-pos 1 4
   in ℚP.positive⁻¹ (+ 1 / 4))
  (ℚRing.solve-∀)

record CanonicalScalarCutset : Set where
  field
    parametersAreCanonical : ClayParameterTuple
    parametersAreCanonical = canonicalClayParameters

    p1ContractionMargin :
      PositiveMargin canonicalCriticalProduct half
    p2KoteckyPreissMargin :
      PositiveMargin canonicalBranchingRatio 1ℚ
    p3FiveTermMargin :
      PositiveMargin canonicalFiveTermLoss canonicalOneStepLossBudget
    p3BetaRemainderMargin :
      PositiveMargin canonicalQuarticRemainderCoefficient
        canonicalOneStepLossBudget
    p5MassTransportMargin :
      PositiveMargin canonicalTransportDefect canonicalTerminalDimensionlessMass

open CanonicalScalarCutset public

canonicalScalarCutset : CanonicalScalarCutset
canonicalScalarCutset = record
  { p1ContractionMargin = canonicalContractionMargin
  ; p2KoteckyPreissMargin = canonicalKPMargin
  ; p3FiveTermMargin = canonicalOneStepMargin
  ; p3BetaRemainderMargin = canonicalBetaRemainderMargin
  ; p5MassTransportMargin = canonicalMassSurvivalMargin
  }

canonicalCommonScalarWitnessLevel : ProofLevel
canonicalCommonScalarWitnessLevel = machineChecked

canonicalCommonScalarPositiveMarginsLevel : ProofLevel
canonicalCommonScalarPositiveMarginsLevel = machineChecked

-- Remaining P4 work is no longer numerical choice.  It is the physical
-- identification theorem showing that the literal P1, P2, P3 and P5 constants
-- are bounded by these five owners at canonicalClayParameters.
canonicalPhysicalConstantIdentificationLevel : ProofLevel
canonicalPhysicalConstantIdentificationLevel = conditional
