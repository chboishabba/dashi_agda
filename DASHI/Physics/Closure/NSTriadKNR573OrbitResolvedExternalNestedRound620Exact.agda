{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNR573OrbitResolvedExternalNestedRound620Exact where

------------------------------------------------------------------------
-- ROUND620 / R573 EXTERNAL NESTED SLOT ON TOTAL ORBIT-RESOLVED RESIDUAL
--
-- R614 represented the external nested slot using R112's nonfixed-only
-- ThreeLegResidualMembership.  R619 now represents the same external forcing
-- on a total proof-relevant fixed/nonfixed orbit carrier.
--
-- This owner ports the R573 external nested companion to that total carrier.
-- It removes the global R112 witness-family dependency from the per-incidence
-- representation layer; the analytic payment remains open.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; cong₂)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNHelicitySignNormalizedCurlRound142Exact as R142
import DASHI.Physics.Closure.NSTriadKNAntiParallelHelicitySlotKernelRound145Exact as R145
import DASHI.Physics.Closure.NSTriadKNCriticalSlotQuadraticKernelRound167Exact as R167
import DASHI.Physics.Closure.NSTriadKNResolventWeightedMixedCommutatorRound294Exact as R294
import DASHI.Physics.Closure.NSTriadKNR573SelfExternalNestedCompanionSplitRound613Exact as R613
import DASHI.Physics.Closure.NSTriadKNExternalWaleffeOrbitResolvedRound619Exact as R619

module OrbitResolvedExternalNested
    {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (W : R294.SwapInvariantCellWeight F)
    (S : Helical.HelicalModeScalars F)
    (L : Helical.PeriodicHelicalProjectorLaws F E I S)
    (H : R142.HelicalHalfCalibration S)
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (velocityTransverse :
      (mode : Z3.FourierMode) →
      Helical.Transverse E mode (Audit.velocity system mode)) where

  module Split =
    R613.NestedNetworkSplit W S L H system velocityTransverse

  velocity = Audit.velocity system

  weightedExternalResolvedSlot :
    (tau : Physical.PhysicalTriadIncidence) →
    R619.ThreeLegOrbitResolvedSelection system tau →
    C3.Complex3 F
  weightedExternalResolvedSlot tau O =
    C3.complex3Scale (R294.weight W tau)
      (C3.complex3Scale (C3.complexI F)
        (R145.slotKernel
          (R167.normalizedDirection E S (Physical.p tau))
          (R167.normalizedDirection E S (Physical.q tau))
          (R619.externalResidualPResolved system tau O)
          (velocity (Physical.q tau))))

  weightedExternalSlotIsOrbitResolved :
    (tau : Physical.PhysicalTriadIncidence) →
    (O : R619.ThreeLegOrbitResolvedSelection system tau) →
    Split.weightedExternalSlot tau
    ≡ weightedExternalResolvedSlot tau O
  weightedExternalSlotIsOrbitResolved tau O =
    cong
      (C3.complex3Scale (R294.weight W tau))
      (cong
        (C3.complex3Scale (C3.complexI F))
        (cong
          (λ forcing →
            R145.slotKernel
              (R167.normalizedDirection E S (Physical.p tau))
              (R167.normalizedDirection E S (Physical.q tau))
              forcing
              (velocity (Physical.q tau)))
          (R619.externalForcingPIsOrbitResolved system tau O)))

  externalResolvedExhaustiveCompanion :
    (tau : Physical.PhysicalTriadIncidence) →
    R619.ThreeLegOrbitResolvedSelection system tau →
    C3.Complex3 F
  externalResolvedExhaustiveCompanion tau O
    with Output.modeEqual (Physical.p tau) Z3.zeroMode
  ... | true = C3.complex3Zero F
  ... | false = weightedExternalResolvedSlot tau O

  externalExhaustiveCompanionIsOrbitResolved :
    (tau : Physical.PhysicalTriadIncidence) →
    (O : R619.ThreeLegOrbitResolvedSelection system tau) →
    Split.externalExhaustiveCompanion tau
    ≡ externalResolvedExhaustiveCompanion tau O
  externalExhaustiveCompanionIsOrbitResolved tau O
    with Output.modeEqual (Physical.p tau) Z3.zeroMode
  ... | true = refl
  ... | false = weightedExternalSlotIsOrbitResolved tau O

  externalResolvedNestedWeightedCompanionCell :
    (tau : Physical.PhysicalTriadIncidence) →
    R619.ThreeLegOrbitResolvedSelection system tau →
    C3.Complex3 F
  externalResolvedNestedWeightedCompanionCell tau O =
    C3.complex3Add
      (externalResolvedExhaustiveCompanion tau O)
      (externalResolvedExhaustiveCompanion tau O)

  externalNestedWeightedCompanionIsOrbitResolved :
    (tau : Physical.PhysicalTriadIncidence) →
    (O : R619.ThreeLegOrbitResolvedSelection system tau) →
    Split.externalNestedWeightedCompanionCell tau
    ≡ externalResolvedNestedWeightedCompanionCell tau O
  externalNestedWeightedCompanionIsOrbitResolved tau O =
    cong₂ C3.complex3Add
      (externalExhaustiveCompanionIsOrbitResolved tau O)
      (externalExhaustiveCompanionIsOrbitResolved tau O)

------------------------------------------------------------------------
-- Status.
------------------------------------------------------------------------

round620ExternalNestedCellTotalGivenOrbitCases : Bool
round620ExternalNestedCellTotalGivenOrbitCases = true

round620RequiresLegacyGlobalR112NonfixedWitnessFamily : Bool
round620RequiresLegacyGlobalR112NonfixedWitnessFamily = false

round620FixedOrbitMultiplicityCorrectionPreserved : Bool
round620FixedOrbitMultiplicityCorrectionPreserved = true

round620ExternalNestedAnalyticPaymentClosed : Bool
round620ExternalNestedAnalyticPaymentClosed = false

round620IntroducesEstimate : Bool
round620IntroducesEstimate = false

round620ExternalNestedCellTotalGivenOrbitCasesIsTrue :
  round620ExternalNestedCellTotalGivenOrbitCases ≡ true
round620ExternalNestedCellTotalGivenOrbitCasesIsTrue = refl

round620RequiresLegacyGlobalR112NonfixedWitnessFamilyIsFalse :
  round620RequiresLegacyGlobalR112NonfixedWitnessFamily ≡ false
round620RequiresLegacyGlobalR112NonfixedWitnessFamilyIsFalse = refl

round620FixedOrbitMultiplicityCorrectionPreservedIsTrue :
  round620FixedOrbitMultiplicityCorrectionPreserved ≡ true
round620FixedOrbitMultiplicityCorrectionPreservedIsTrue = refl

round620ExternalNestedAnalyticPaymentClosedIsFalse :
  round620ExternalNestedAnalyticPaymentClosed ≡ false
round620ExternalNestedAnalyticPaymentClosedIsFalse = refl

round620IntroducesEstimateIsFalse :
  round620IntroducesEstimate ≡ false
round620IntroducesEstimateIsFalse = refl
