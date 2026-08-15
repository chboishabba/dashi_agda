module DASHI.Physics.Closure.NSTriadKNLuoFixedShiftRecursionReductionExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale--Kato--Majda Criterion with Optimal Frequency and
-- Temporal Localization".
-- Journal of Mathematical Fluid Mechanics 21 (2019), article 1.
-- DOI: 10.1007/s00021-019-0411-z.
-- arXiv DOI: 10.48550/arXiv.1803.05569.
--
-- PURPOSE
-- Close the order-theoretic part of Luo's fixed-shift recursion.  The physical
-- proof now only has to establish the integrated cutoff-energy inequality and
-- the semantic fact that its selected maximum is below energy+dissipation.
-- Their composition gives the exact recursion field consumed by the existing
-- fixed-block induction.  Flux-correction absorption is likewise reduced to
-- an exact physical flux bound followed by a target comparison.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; _+_; _*_; _≤_)
import Data.Rational.Properties as ℚₚ

record FixedShiftRecursionPhysicalData : Set₁ where
  field
    cutoffEnergy cutoffDissipation : Nat → ℚ
    predecessorByFixedShift : Nat → Nat
    correctedShiftCoefficient : ℚ
    integratedFluxCorrection : Nat → ℚ
    selectedMaximum : ℚ → ℚ → ℚ
    sufficientlyLarge : Nat → Set

    maximumBelowEnergyDissipationSum :
      (shell : Nat) →
      selectedMaximum
        (cutoffEnergy shell)
        (cutoffDissipation shell)
      ≤ cutoffEnergy shell + cutoffDissipation shell

    integratedCutoffEnergyInequality :
      (shell : Nat) → sufficientlyLarge shell →
      cutoffEnergy shell + cutoffDissipation shell
      ≤ correctedShiftCoefficient
          * cutoffDissipation (predecessorByFixedShift shell)
        + integratedFluxCorrection shell

open FixedShiftRecursionPhysicalData public

fixedShiftRecursionFromCutoffEnergy :
  (physicalData : FixedShiftRecursionPhysicalData) →
  (shell : Nat) → sufficientlyLarge physicalData shell →
  selectedMaximum physicalData
    (cutoffEnergy physicalData shell)
    (cutoffDissipation physicalData shell)
  ≤ correctedShiftCoefficient physicalData
      * cutoffDissipation physicalData
          (predecessorByFixedShift physicalData shell)
    + integratedFluxCorrection physicalData shell
fixedShiftRecursionFromCutoffEnergy physicalData shell large =
  ℚₚ.≤-trans
    (maximumBelowEnergyDissipationSum physicalData shell)
    (integratedCutoffEnergyInequality physicalData shell large)

record FluxCorrectionAbsorptionData : Set₁ where
  field
    integratedFluxCorrection physicalFluxMajorant dyadicDecayTarget : Nat → ℚ
    sufficientlyLarge : Nat → Set

    integratedFluxBelowPhysicalMajorant :
      (shell : Nat) → sufficientlyLarge shell →
      integratedFluxCorrection shell ≤ physicalFluxMajorant shell

    physicalMajorantBelowDecayTarget :
      (shell : Nat) → sufficientlyLarge shell →
      physicalFluxMajorant shell ≤ dyadicDecayTarget shell

open FluxCorrectionAbsorptionData public

fluxCorrectionAbsorbedFromPhysicalMajorant :
  (physicalData : FluxCorrectionAbsorptionData) →
  (shell : Nat) → sufficientlyLarge physicalData shell →
  integratedFluxCorrection physicalData shell
    ≤ dyadicDecayTarget physicalData shell
fluxCorrectionAbsorbedFromPhysicalMajorant physicalData shell large =
  ℚₚ.≤-trans
    (integratedFluxBelowPhysicalMajorant physicalData shell large)
    (physicalMajorantBelowDecayTarget physicalData shell large)

fixedShiftOrderReductionClosed : Bool
fixedShiftOrderReductionClosed = true

fluxCorrectionAbsorptionReductionClosed : Bool
fluxCorrectionAbsorptionReductionClosed = true

fixedShiftOrderReductionClosedIsTrue :
  fixedShiftOrderReductionClosed ≡ true
fixedShiftOrderReductionClosedIsTrue = refl

fluxCorrectionAbsorptionReductionClosedIsTrue :
  fluxCorrectionAbsorptionReductionClosed ≡ true
fluxCorrectionAbsorptionReductionClosedIsTrue = refl
