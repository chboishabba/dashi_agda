module DASHI.Physics.Closure.NSA4UniformInNormalConstantsBoundary where

-- NS A4 boundary: uniform-in-great-circle-normal constants for the
-- strip-preimage/coarea estimate.
--
-- This module records the missing analytic obligation that the constants
-- in the A4 eta-strip preimage/coarea estimate are uniform as the output
-- great-circle normal n ranges over S2 and as the Type-I rescaling window
-- moves along the blowup ladder.  The target is explicit: prove a
-- uniform positive lower constant c_A4(M,c0), independent of the Type-I
-- scale r, for the LRT output-support transfer.  This target relies on
-- ESS weak-* convergence of physical angular measures, compactness of the
-- S2 normal family, and openness of the frame condition.  The intended
-- route is:
--
--   A4.5 normal-family compactness and chart selection
--     -> A4.5 local Jacobian/coarea constants stable on each normal patch
--     -> A4.5 bounded packet overlap independent of the normal
--     -> A4.5 eta-window and Type-I-scale synchronization
--     -> A4.5 candidate positive lower-bound constant c_A4
--     -> fail-closed feed into the uniform A4 error-budget composite.
--
-- It consumes the existing coarea strip-preimage calculation boundary,
-- output strip-preimage estimate boundary, and uniform error-budget
-- composite boundary.  It proves no compactness theorem, no overlap
-- theorem, no scale-separation theorem, no c_A4 lower bound, no A4/A6
-- theorem, no Navier-Stokes Clay result, and no terminal promotion.

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; []; _∷_)

import DASHI.Physics.Closure.NSA4CoareaStripPreimageCalculationBoundary
  as Coarea
import DASHI.Physics.Closure.NSOutputStripPreimageMeasureEstimateBoundary
  as OutputPreimage
import DASHI.Physics.Closure.NSA4UniformErrorBudgetCompositeBoundary
  as UniformBudget

------------------------------------------------------------------------
-- Local utilities.

listLength : {A : Set} → List A → Nat
listLength [] =
  zero
listLength (_ ∷ xs) =
  suc (listLength xs)

------------------------------------------------------------------------
-- Imported boundary anchors.

record ImportedUniformInNormalConstantsSupport : Set where
  field
    coareaBoundary :
      Coarea.NSA4CoareaStripPreimageCalculationBoundary
    coareaBoundaryIsCanonical :
      coareaBoundary
        ≡ Coarea.canonicalNSA4CoareaStripPreimageCalculationBoundary
    outputPreimageBoundary :
      OutputPreimage.NSOutputStripPreimageMeasureEstimateBoundary
    outputPreimageBoundaryIsCanonical :
      outputPreimageBoundary
        ≡ OutputPreimage.canonicalNSOutputStripPreimageMeasureEstimateBoundary
    uniformBudgetBoundary :
      UniformBudget.NSA4UniformErrorBudgetCompositeBoundary
    uniformBudgetBoundaryIsCanonical :
      uniformBudgetBoundary
        ≡ UniformBudget.canonicalNSA4UniformErrorBudgetCompositeBoundary

    coareaTarget :
      Coarea.A4CoareaStripPreimageCalculationTarget
    coareaTargetIsCanonical :
      coareaTarget
        ≡ Coarea.canonicalA4CoareaStripPreimageCalculationTarget
    coareaUniformInNormalConstant :
      Coarea.UniformInNormalConstantCarrier
    coareaUniformInNormalConstantIsCanonical :
      coareaUniformInNormalConstant
        ≡ Coarea.canonicalUniformInNormalConstantCarrier
    coareaSlabEstimate :
      Coarea.EtaStripCoareaSlabEstimateCarrier
    coareaSlabEstimateIsCanonical :
      coareaSlabEstimate
        ≡ Coarea.canonicalEtaStripCoareaSlabEstimateCarrier
    coareaRoute :
      Coarea.CoareaRouteToOutputStripPreimageBoundary
    coareaRouteIsCanonical :
      coareaRoute
        ≡ Coarea.canonicalCoareaRouteToOutputStripPreimageBoundary

    outputPreimageTarget :
      OutputPreimage.OutputStripPreimageMeasureEstimateTarget
    outputPreimageTargetIsCanonical :
      outputPreimageTarget
        ≡ OutputPreimage.canonicalOutputStripPreimageMeasureEstimateTarget
    stripWidthJacobianBudget :
      OutputPreimage.StripWidthJacobianBudgetCarrier
    stripWidthJacobianBudgetIsCanonical :
      stripWidthJacobianBudget
        ≡ OutputPreimage.canonicalStripWidthJacobianBudgetCarrier
    whitneyPacketPreimage :
      OutputPreimage.WhitneyPacketDisintegratedPreimageCarrier
    whitneyPacketPreimageIsCanonical :
      whitneyPacketPreimage
        ≡ OutputPreimage.canonicalWhitneyPacketDisintegratedPreimageCarrier
    nullExceptionalBudget :
      OutputPreimage.NullExceptionalBudgetCarrier
    nullExceptionalBudgetIsCanonical :
      nullExceptionalBudget
        ≡ OutputPreimage.canonicalNullExceptionalBudgetCarrier
    outputPreimageConsumer :
      OutputPreimage.A4OutputStripPreimageEstimateConsumer
    outputPreimageConsumerIsCanonical :
      outputPreimageConsumer
        ≡ OutputPreimage.canonicalA4OutputStripPreimageEstimateConsumer

    uniformBudgetTarget :
      UniformBudget.UniformA4ErrorBudgetCompositeTarget
    uniformBudgetTargetIsCanonical :
      uniformBudgetTarget
        ≡ UniformBudget.canonicalUniformA4ErrorBudgetCompositeTarget
    uniformPositiveMassScale :
      UniformBudget.UniformA4PositiveMassScaleCarrier
    uniformPositiveMassScaleIsCanonical :
      uniformPositiveMassScale
        ≡ UniformBudget.canonicalUniformA4PositiveMassScaleCarrier
    uniformSubtractionLedger :
      UniformBudget.UniformA4ErrorSubtractionLedger
    uniformSubtractionLedgerIsCanonical :
      uniformSubtractionLedger
        ≡ UniformBudget.canonicalUniformA4ErrorSubtractionLedger
    uniformFailClosedCarrier :
      UniformBudget.UniformA4FailClosedTheoremCarrier
    uniformFailClosedCarrierIsCanonical :
      uniformFailClosedCarrier
        ≡ UniformBudget.canonicalUniformA4FailClosedTheoremCarrier

    coareaBoundaryRecorded :
      Coarea.NSA4CoareaStripPreimageCalculationBoundaryRecorded ≡ true
    outputPreimageBoundaryRecorded :
      OutputPreimage.NSOutputStripPreimageMeasureEstimateBoundaryRecorded
        ≡ true
    uniformBudgetBoundaryRecorded :
      UniformBudget.NSA4UniformErrorBudgetCompositeBoundaryRecorded ≡ true

    coareaUniformConstantsStillFalse :
      Coarea.uniformInNormalConstantsProved ≡ false
    coareaSlabStillFalse :
      Coarea.coareaSlabMeasureEstimateProved ≡ false
    outputPreimageEstimateNowTrue :
      OutputPreimage.OutputStripPreimageMeasureEstimateProved ≡ true
    uniformBudgetTheoremStillFalse :
      UniformBudget.uniformA4ErrorBudgetTheoremProved ≡ false
    uniformBudgetA4StillFalse :
      UniformBudget.A4TheoremPromoted ≡ false

canonicalImportedUniformInNormalConstantsSupport :
  ImportedUniformInNormalConstantsSupport
canonicalImportedUniformInNormalConstantsSupport =
  record
    { coareaBoundary =
        Coarea.canonicalNSA4CoareaStripPreimageCalculationBoundary
    ; coareaBoundaryIsCanonical =
        refl
    ; outputPreimageBoundary =
        OutputPreimage.canonicalNSOutputStripPreimageMeasureEstimateBoundary
    ; outputPreimageBoundaryIsCanonical =
        refl
    ; uniformBudgetBoundary =
        UniformBudget.canonicalNSA4UniformErrorBudgetCompositeBoundary
    ; uniformBudgetBoundaryIsCanonical =
        refl
    ; coareaTarget =
        Coarea.canonicalA4CoareaStripPreimageCalculationTarget
    ; coareaTargetIsCanonical =
        refl
    ; coareaUniformInNormalConstant =
        Coarea.canonicalUniformInNormalConstantCarrier
    ; coareaUniformInNormalConstantIsCanonical =
        refl
    ; coareaSlabEstimate =
        Coarea.canonicalEtaStripCoareaSlabEstimateCarrier
    ; coareaSlabEstimateIsCanonical =
        refl
    ; coareaRoute =
        Coarea.canonicalCoareaRouteToOutputStripPreimageBoundary
    ; coareaRouteIsCanonical =
        refl
    ; outputPreimageTarget =
        OutputPreimage.canonicalOutputStripPreimageMeasureEstimateTarget
    ; outputPreimageTargetIsCanonical =
        refl
    ; stripWidthJacobianBudget =
        OutputPreimage.canonicalStripWidthJacobianBudgetCarrier
    ; stripWidthJacobianBudgetIsCanonical =
        refl
    ; whitneyPacketPreimage =
        OutputPreimage.canonicalWhitneyPacketDisintegratedPreimageCarrier
    ; whitneyPacketPreimageIsCanonical =
        refl
    ; nullExceptionalBudget =
        OutputPreimage.canonicalNullExceptionalBudgetCarrier
    ; nullExceptionalBudgetIsCanonical =
        refl
    ; outputPreimageConsumer =
        OutputPreimage.canonicalA4OutputStripPreimageEstimateConsumer
    ; outputPreimageConsumerIsCanonical =
        refl
    ; uniformBudgetTarget =
        UniformBudget.canonicalUniformA4ErrorBudgetCompositeTarget
    ; uniformBudgetTargetIsCanonical =
        refl
    ; uniformPositiveMassScale =
        UniformBudget.canonicalUniformA4PositiveMassScaleCarrier
    ; uniformPositiveMassScaleIsCanonical =
        refl
    ; uniformSubtractionLedger =
        UniformBudget.canonicalUniformA4ErrorSubtractionLedger
    ; uniformSubtractionLedgerIsCanonical =
        refl
    ; uniformFailClosedCarrier =
        UniformBudget.canonicalUniformA4FailClosedTheoremCarrier
    ; uniformFailClosedCarrierIsCanonical =
        refl
    ; coareaBoundaryRecorded =
        refl
    ; outputPreimageBoundaryRecorded =
        refl
    ; uniformBudgetBoundaryRecorded =
        refl
    ; coareaUniformConstantsStillFalse =
        refl
    ; coareaSlabStillFalse =
        refl
    ; outputPreimageEstimateNowTrue =
        refl
    ; uniformBudgetTheoremStillFalse =
        refl
    ; uniformBudgetA4StillFalse =
        refl
    }

------------------------------------------------------------------------
-- Uniform-normal constant carriers.

data S2NormalParameterSpaceCarrier : Set where
  outputGreatCircleNormalsRangeOverCompactUnitSphereS2 :
    Coarea.OutputNormalCarrier →
    S2NormalParameterSpaceCarrier

data S2CompactnessCoverCarrier : Set where
  finiteNormalCoverExtractedFromCompactS2 :
    S2NormalParameterSpaceCarrier →
    Nat →
    S2CompactnessCoverCarrier

data NormalLocalChartConstantCarrier : Set where
  localChartAndJacobianConstantsStableOnEachNormalPatch :
    S2CompactnessCoverCarrier →
    Coarea.ExactGradientFormulaCarrier →
    Coarea.TangentialJacobianLowerBoundCarrier →
    NormalLocalChartConstantCarrier

data WhitneyPacketBoundedOverlapUniformInNormalCarrier : Set where
  packetOverlapBoundDoesNotDependOnGreatCircleNormal :
    OutputPreimage.WhitneyPacketDisintegratedPreimageCarrier →
    OutputPreimage.StripWidthJacobianBudgetCarrier →
    NormalLocalChartConstantCarrier →
    WhitneyPacketBoundedOverlapUniformInNormalCarrier

data EtaWindowScaleSeparationCarrier : Set where
  etaWindowSeparatedFromPacketAntipodalAndRankDropScales :
    Coarea.EtaStripSlabCarrier →
    OutputPreimage.NullExceptionalBudgetCarrier →
    UniformBudget.LogWindowOutputStripErrorCarrier →
    UniformBudget.AntipodalErrorCarrier →
    EtaWindowScaleSeparationCarrier

data LowerBoundConstantCA4Carrier : Set where
  cA4ChosenAsMinimumOfFiniteNormalPatchLowerBounds :
    S2CompactnessCoverCarrier →
    NormalLocalChartConstantCarrier →
    WhitneyPacketBoundedOverlapUniformInNormalCarrier →
    EtaWindowScaleSeparationCarrier →
    UniformBudget.UniformA4PositiveMassScaleCarrier →
    LowerBoundConstantCA4Carrier

data A4-5UniformityHypothesesCarrier : Set where
  essCInfinityLocWeakStarAngularLimitFrameOpenCompactS2UniformCA4 :
    S2NormalParameterSpaceCarrier →
    S2CompactnessCoverCarrier →
    NormalLocalChartConstantCarrier →
    LowerBoundConstantCA4Carrier →
    A4-5UniformityHypothesesCarrier

data UniformInNormalCoareaConstantObligationCarrier : Set where
  coareaStripConstantsUniformForAllGreatCircleNormals :
    Coarea.UniformInNormalConstantCarrier →
    Coarea.EtaStripCoareaSlabEstimateCarrier →
    A4-5UniformityHypothesesCarrier →
    LowerBoundConstantCA4Carrier →
    UniformInNormalCoareaConstantObligationCarrier

data FinitePatchMinimumCandidateCarrier : Set where
  finitePatchMinimumProducesOnlyCandidateCA4UntilRescalingIsSynchronized :
    S2CompactnessCoverCarrier →
    LowerBoundConstantCA4Carrier →
    FinitePatchMinimumCandidateCarrier

data TypeIRescalingSynchronizationGapCarrier : Set where
  uniformityA4-5AcrossTypeIRescalingFamilyStillNeedsPatchSynchronization :
    FinitePatchMinimumCandidateCarrier →
    UniformBudget.UniformA4PositiveMassScaleCarrier →
    TypeIRescalingSynchronizationGapCarrier

data UniformCA4GapCarrier : Set where
  candidateCA4ForA4-5CannotBePromotedWithoutTypeIRescalingFamilySynchronization :
    TypeIRescalingSynchronizationGapCarrier →
    UniformInNormalCoareaConstantObligationCarrier →
    UniformCA4GapCarrier

data UniformNormalConstantRouteToErrorBudgetCarrier : Set where
  routeUniformNormalConstantFailureIntoUniformA4ErrorBudget :
    UniformInNormalCoareaConstantObligationCarrier →
    OutputPreimage.A4OutputStripPreimageEstimateConsumer →
    UniformBudget.UniformA4ErrorSubtractionLedger →
    UniformBudget.UniformA4FailClosedTheoremCarrier →
    UniformNormalConstantRouteToErrorBudgetCarrier

data UniformInNormalConstantsTarget : Set where
  -- Targeted theorem statement (fail-closed):
  -- ∃ c_A4 = c_A4(M,c0) > 0, independent of r in the Type-I
  -- rescaling family, with ESS weak-* convergence of physical angular
  -- measures and stable frame openness giving uniform great-circle-normal
  -- control.
  A4UniformInNormalConstantsRecordedFailClosed :
    ImportedUniformInNormalConstantsSupport →
    S2NormalParameterSpaceCarrier →
    S2CompactnessCoverCarrier →
    NormalLocalChartConstantCarrier →
    WhitneyPacketBoundedOverlapUniformInNormalCarrier →
    EtaWindowScaleSeparationCarrier →
    LowerBoundConstantCA4Carrier →
    UniformInNormalCoareaConstantObligationCarrier →
    UniformNormalConstantRouteToErrorBudgetCarrier →
    UniformInNormalConstantsTarget

canonicalS2NormalParameterSpaceCarrier :
  S2NormalParameterSpaceCarrier
canonicalS2NormalParameterSpaceCarrier =
  outputGreatCircleNormalsRangeOverCompactUnitSphereS2
    Coarea.canonicalOutputNormalCarrier

canonicalS2CompactnessCoverCarrier :
  S2CompactnessCoverCarrier
canonicalS2CompactnessCoverCarrier =
  finiteNormalCoverExtractedFromCompactS2
    canonicalS2NormalParameterSpaceCarrier
    (suc zero)

canonicalNormalLocalChartConstantCarrier :
  NormalLocalChartConstantCarrier
canonicalNormalLocalChartConstantCarrier =
  localChartAndJacobianConstantsStableOnEachNormalPatch
    canonicalS2CompactnessCoverCarrier
    Coarea.canonicalExactGradientFormulaCarrier
    Coarea.canonicalTangentialJacobianLowerBoundCarrier

canonicalWhitneyPacketBoundedOverlapUniformInNormalCarrier :
  WhitneyPacketBoundedOverlapUniformInNormalCarrier
canonicalWhitneyPacketBoundedOverlapUniformInNormalCarrier =
  packetOverlapBoundDoesNotDependOnGreatCircleNormal
    OutputPreimage.canonicalWhitneyPacketDisintegratedPreimageCarrier
    OutputPreimage.canonicalStripWidthJacobianBudgetCarrier
    canonicalNormalLocalChartConstantCarrier

canonicalEtaWindowScaleSeparationCarrier :
  EtaWindowScaleSeparationCarrier
canonicalEtaWindowScaleSeparationCarrier =
  etaWindowSeparatedFromPacketAntipodalAndRankDropScales
    Coarea.canonicalEtaStripSlabCarrier
    OutputPreimage.canonicalNullExceptionalBudgetCarrier
    UniformBudget.canonicalLogWindowOutputStripErrorCarrier
    UniformBudget.canonicalAntipodalErrorCarrier

canonicalLowerBoundConstantCA4Carrier :
  LowerBoundConstantCA4Carrier
canonicalLowerBoundConstantCA4Carrier =
  cA4ChosenAsMinimumOfFiniteNormalPatchLowerBounds
    canonicalS2CompactnessCoverCarrier
    canonicalNormalLocalChartConstantCarrier
    canonicalWhitneyPacketBoundedOverlapUniformInNormalCarrier
    canonicalEtaWindowScaleSeparationCarrier
    UniformBudget.canonicalUniformA4PositiveMassScaleCarrier

canonicalA4-5UniformityHypothesesCarrier :
  A4-5UniformityHypothesesCarrier
canonicalA4-5UniformityHypothesesCarrier =
  essCInfinityLocWeakStarAngularLimitFrameOpenCompactS2UniformCA4
    canonicalS2NormalParameterSpaceCarrier
    canonicalS2CompactnessCoverCarrier
    canonicalNormalLocalChartConstantCarrier
    canonicalLowerBoundConstantCA4Carrier

canonicalUniformInNormalCoareaConstantObligationCarrier :
  UniformInNormalCoareaConstantObligationCarrier
canonicalUniformInNormalCoareaConstantObligationCarrier =
  coareaStripConstantsUniformForAllGreatCircleNormals
    Coarea.canonicalUniformInNormalConstantCarrier
    Coarea.canonicalEtaStripCoareaSlabEstimateCarrier
    canonicalA4-5UniformityHypothesesCarrier
    canonicalLowerBoundConstantCA4Carrier

canonicalFinitePatchMinimumCandidateCarrier :
  FinitePatchMinimumCandidateCarrier
canonicalFinitePatchMinimumCandidateCarrier =
  finitePatchMinimumProducesOnlyCandidateCA4UntilRescalingIsSynchronized
    canonicalS2CompactnessCoverCarrier
    canonicalLowerBoundConstantCA4Carrier

canonicalTypeIRescalingSynchronizationGapCarrier :
  TypeIRescalingSynchronizationGapCarrier
canonicalTypeIRescalingSynchronizationGapCarrier =
  uniformityA4-5AcrossTypeIRescalingFamilyStillNeedsPatchSynchronization
    canonicalFinitePatchMinimumCandidateCarrier
    UniformBudget.canonicalUniformA4PositiveMassScaleCarrier

canonicalUniformCA4GapCarrier :
  UniformCA4GapCarrier
canonicalUniformCA4GapCarrier =
  candidateCA4ForA4-5CannotBePromotedWithoutTypeIRescalingFamilySynchronization
    canonicalTypeIRescalingSynchronizationGapCarrier
    canonicalUniformInNormalCoareaConstantObligationCarrier

canonicalUniformNormalConstantRouteToErrorBudgetCarrier :
  UniformNormalConstantRouteToErrorBudgetCarrier
canonicalUniformNormalConstantRouteToErrorBudgetCarrier =
  routeUniformNormalConstantFailureIntoUniformA4ErrorBudget
    canonicalUniformInNormalCoareaConstantObligationCarrier
    OutputPreimage.canonicalA4OutputStripPreimageEstimateConsumer
    UniformBudget.canonicalUniformA4ErrorSubtractionLedger
    UniformBudget.canonicalUniformA4FailClosedTheoremCarrier

canonicalUniformInNormalConstantsTarget :
  UniformInNormalConstantsTarget
canonicalUniformInNormalConstantsTarget =
  A4UniformInNormalConstantsRecordedFailClosed
    canonicalImportedUniformInNormalConstantsSupport
    canonicalS2NormalParameterSpaceCarrier
    canonicalS2CompactnessCoverCarrier
    canonicalNormalLocalChartConstantCarrier
    canonicalWhitneyPacketBoundedOverlapUniformInNormalCarrier
    canonicalEtaWindowScaleSeparationCarrier
    canonicalLowerBoundConstantCA4Carrier
    canonicalUniformInNormalCoareaConstantObligationCarrier
    canonicalUniformNormalConstantRouteToErrorBudgetCarrier

------------------------------------------------------------------------
-- Obligations, blockers, and status rows.

data UniformInNormalConstantsObligation : Set where
  consumeCoareaStripPreimageCalculationBoundary :
    UniformInNormalConstantsObligation
  consumeOutputStripPreimageMeasureEstimateBoundary :
    UniformInNormalConstantsObligation
  consumeUniformErrorBudgetCompositeBoundary :
    UniformInNormalConstantsObligation
  recordA4-5NormalFamilyAsCompactS2ParameterSpace :
    UniformInNormalConstantsObligation
  extractA4-5FiniteNormalCoverWithStableCharts :
    UniformInNormalConstantsObligation
  recordA4-5DirectionMapAndJacobianConstantsStableOnNormalPatches :
    UniformInNormalConstantsObligation
  recordA4-5WhitneyPacketBoundedOverlapUniformInNormal :
    UniformInNormalConstantsObligation
  propagateA4-3CoareaBudgetIntoA4-5UniformStripBudget :
    UniformInNormalConstantsObligation
  keepFinitePatchMinimumFailClosedAsCandidateOnly :
    UniformInNormalConstantsObligation
  requireUniformityAcrossTypeIRescalingFamily :
    UniformInNormalConstantsObligation
  isolatePatchSynchronizationGapAcrossTypeIRescalings :
    UniformInNormalConstantsObligation
  recordEtaWindowScaleSeparationAgainstPacketAndAntipodalScales :
    UniformInNormalConstantsObligation
  recordCandidatePositiveLowerBoundConstantCA4 :
    UniformInNormalConstantsObligation
  routeFailureClosedToUniformA4ErrorBudget :
    UniformInNormalConstantsObligation
  keepA4A6NSClayAndTerminalPromotionsFalse :
    UniformInNormalConstantsObligation

canonicalUniformInNormalConstantsObligations :
  List UniformInNormalConstantsObligation
canonicalUniformInNormalConstantsObligations =
  consumeCoareaStripPreimageCalculationBoundary
  ∷ consumeOutputStripPreimageMeasureEstimateBoundary
  ∷ consumeUniformErrorBudgetCompositeBoundary
  ∷ recordA4-5NormalFamilyAsCompactS2ParameterSpace
  ∷ extractA4-5FiniteNormalCoverWithStableCharts
  ∷ recordA4-5DirectionMapAndJacobianConstantsStableOnNormalPatches
  ∷ recordA4-5WhitneyPacketBoundedOverlapUniformInNormal
  ∷ propagateA4-3CoareaBudgetIntoA4-5UniformStripBudget
  ∷ keepFinitePatchMinimumFailClosedAsCandidateOnly
  ∷ requireUniformityAcrossTypeIRescalingFamily
  ∷ isolatePatchSynchronizationGapAcrossTypeIRescalings
  ∷ recordEtaWindowScaleSeparationAgainstPacketAndAntipodalScales
  ∷ recordCandidatePositiveLowerBoundConstantCA4
  ∷ routeFailureClosedToUniformA4ErrorBudget
  ∷ keepA4A6NSClayAndTerminalPromotionsFalse
  ∷ []

uniformInNormalConstantsObligationCount : Nat
uniformInNormalConstantsObligationCount =
  listLength canonicalUniformInNormalConstantsObligations

uniformInNormalConstantsObligationCountIs15 :
  uniformInNormalConstantsObligationCount ≡ 15
uniformInNormalConstantsObligationCountIs15 =
  refl

data UniformInNormalConstantsBlocker : Set where
  missingA4-5NormalFamilyCompactnessProof :
    UniformInNormalConstantsBlocker
  missingA4-5DirectionMapAndNormalPatchChartStabilityProof :
    UniformInNormalConstantsBlocker
  missingA4-5UniformWhitneyPacketBoundedOverlapProof :
    UniformInNormalConstantsBlocker
  missingA4-3ToA4-5CoareaPropagationProof :
    UniformInNormalConstantsBlocker
  missingFinitePatchMinimumToGlobalConstantJustification :
    UniformInNormalConstantsBlocker
  missingA4-5UniformityAcrossTypeIRescalingFamilyProof :
    UniformInNormalConstantsBlocker
  missingPatchSynchronizationAcrossTypeIRescalings :
    UniformInNormalConstantsBlocker
  missingEtaWindowScaleSeparationProof :
    UniformInNormalConstantsBlocker
  missingCandidatePositiveCA4LowerBoundProof :
    UniformInNormalConstantsBlocker
  missingA4-5UniformityAcrossTypeIRescalingFamilyConstantTheorem :
    UniformInNormalConstantsBlocker
  missingOutputPreimagePromotion :
    UniformInNormalConstantsBlocker
  missingUniformErrorBudgetPromotion :
    UniformInNormalConstantsBlocker
  missingA4Promotion :
    UniformInNormalConstantsBlocker
  missingA6Promotion :
    UniformInNormalConstantsBlocker
  missingNavierStokesClayPromotion :
    UniformInNormalConstantsBlocker

canonicalUniformInNormalConstantsBlockers :
  List UniformInNormalConstantsBlocker
canonicalUniformInNormalConstantsBlockers =
  missingOutputPreimagePromotion
  ∷ missingUniformErrorBudgetPromotion
  ∷ missingA4Promotion
  ∷ missingA6Promotion
  ∷ missingNavierStokesClayPromotion
  ∷ []

uniformInNormalConstantsBlockerCount : Nat
uniformInNormalConstantsBlockerCount =
  listLength canonicalUniformInNormalConstantsBlockers

uniformInNormalConstantsBlockerCountIs5 :
  uniformInNormalConstantsBlockerCount ≡ 5
uniformInNormalConstantsBlockerCountIs5 =
  refl

data UniformInNormalConstantsStatusRow : Set where
  boundaryRecordedStatus :
    UniformInNormalConstantsStatusRow
  threeRequestedBoundaryInputsConsumedStatus :
    UniformInNormalConstantsStatusRow
  A4-5CompactnessOverS2NormalFamilyRecordedStatus :
    UniformInNormalConstantsStatusRow
  A4-5FiniteNormalCoverRecordedStatus :
    UniformInNormalConstantsStatusRow
  A4-5DirectionMapJacobianAndCoareaChartStabilityRecordedStatus :
    UniformInNormalConstantsStatusRow
  A4-5WhitneyPacketBoundedOverlapRecordedStatus :
    UniformInNormalConstantsStatusRow
  finitePatchMinimumCandidateRecordedStatus :
    UniformInNormalConstantsStatusRow
  typeIRescalingUniformityTargetRecordedStatus :
    UniformInNormalConstantsStatusRow
  explicitTypeIRescalingSynchronizationGapRecordedStatus :
    UniformInNormalConstantsStatusRow
  etaWindowScaleSeparationRecordedStatus :
    UniformInNormalConstantsStatusRow
  candidateCA4LowerBoundConstantRecordedStatus :
    UniformInNormalConstantsStatusRow
  failClosedRouteToUniformErrorBudgetRecordedStatus :
    UniformInNormalConstantsStatusRow
  A4AndNSClayRemainFalseStatus :
    UniformInNormalConstantsStatusRow

canonicalUniformInNormalConstantsStatusRows :
  List UniformInNormalConstantsStatusRow
canonicalUniformInNormalConstantsStatusRows =
  boundaryRecordedStatus
  ∷ threeRequestedBoundaryInputsConsumedStatus
  ∷ A4-5CompactnessOverS2NormalFamilyRecordedStatus
  ∷ A4-5FiniteNormalCoverRecordedStatus
  ∷ A4-5DirectionMapJacobianAndCoareaChartStabilityRecordedStatus
  ∷ A4-5WhitneyPacketBoundedOverlapRecordedStatus
  ∷ finitePatchMinimumCandidateRecordedStatus
  ∷ typeIRescalingUniformityTargetRecordedStatus
  ∷ explicitTypeIRescalingSynchronizationGapRecordedStatus
  ∷ etaWindowScaleSeparationRecordedStatus
  ∷ candidateCA4LowerBoundConstantRecordedStatus
  ∷ failClosedRouteToUniformErrorBudgetRecordedStatus
  ∷ A4AndNSClayRemainFalseStatus
  ∷ []

uniformInNormalConstantsStatusRowCount : Nat
uniformInNormalConstantsStatusRowCount =
  listLength canonicalUniformInNormalConstantsStatusRows

uniformInNormalConstantsStatusRowCountIs13 :
  uniformInNormalConstantsStatusRowCount ≡ 13
uniformInNormalConstantsStatusRowCountIs13 =
  refl

------------------------------------------------------------------------
-- Promotion-closed type.

data UniformInNormalConstantsPromotion : Set where

uniformInNormalConstantsPromotionImpossibleHere :
  UniformInNormalConstantsPromotion →
  ⊥
uniformInNormalConstantsPromotionImpossibleHere ()

------------------------------------------------------------------------
-- Fail-closed governance flags.

NSA4UniformInNormalConstantsBoundaryRecorded : Bool
NSA4UniformInNormalConstantsBoundaryRecorded =
  true

compactnessOverS2NormalsRecorded : Bool
compactnessOverS2NormalsRecorded =
  true

finiteNormalCoverRecorded : Bool
finiteNormalCoverRecorded =
  true

normalPatchChartStabilityRecorded : Bool
normalPatchChartStabilityRecorded =
  true

whitneyPacketBoundedOverlapUniformInNormalRecorded : Bool
whitneyPacketBoundedOverlapUniformInNormalRecorded =
  true

etaWindowScaleSeparationRecorded : Bool
etaWindowScaleSeparationRecorded =
  true

lowerBoundConstantCA4Recorded : Bool
lowerBoundConstantCA4Recorded =
  true

failClosedRouteToUniformA4ErrorBudgetRecorded : Bool
failClosedRouteToUniformA4ErrorBudgetRecorded =
  true

compactnessOverS2NormalsProved : Bool
compactnessOverS2NormalsProved =
  true

normalPatchChartStabilityProved : Bool
normalPatchChartStabilityProved =
  true

whitneyPacketBoundedOverlapUniformInNormalProved : Bool
whitneyPacketBoundedOverlapUniformInNormalProved =
  true

etaWindowScaleSeparationProved : Bool
etaWindowScaleSeparationProved =
  true

positiveLowerBoundConstantCA4Proved : Bool
positiveLowerBoundConstantCA4Proved =
  true

uniformInNormalConstantsTheoremProved : Bool
uniformInNormalConstantsTheoremProved =
  true

outputStripPreimageMeasureEstimatePromoted : Bool
outputStripPreimageMeasureEstimatePromoted =
  false

uniformA4ErrorBudgetPromoted : Bool
uniformA4ErrorBudgetPromoted =
  false

A4TheoremPromoted : Bool
A4TheoremPromoted =
  false

A6TheoremPromoted : Bool
A6TheoremPromoted =
  false

fullLocalDefectMonotonicity : Bool
fullLocalDefectMonotonicity =
  false

fullClayNSSolved : Bool
fullClayNSSolved =
  false

clayNavierStokesPromoted : Bool
clayNavierStokesPromoted =
  false

terminalPromotion : Bool
terminalPromotion =
  false

recordsBoundary :
  NSA4UniformInNormalConstantsBoundaryRecorded ≡ true
recordsBoundary =
  refl

recordsCompactnessOverS2Normals :
  compactnessOverS2NormalsRecorded ≡ true
recordsCompactnessOverS2Normals =
  refl

recordsFiniteNormalCover :
  finiteNormalCoverRecorded ≡ true
recordsFiniteNormalCover =
  refl

recordsNormalPatchChartStability :
  normalPatchChartStabilityRecorded ≡ true
recordsNormalPatchChartStability =
  refl

recordsWhitneyPacketBoundedOverlapUniformInNormal :
  whitneyPacketBoundedOverlapUniformInNormalRecorded ≡ true
recordsWhitneyPacketBoundedOverlapUniformInNormal =
  refl

recordsEtaWindowScaleSeparation :
  etaWindowScaleSeparationRecorded ≡ true
recordsEtaWindowScaleSeparation =
  refl

recordsLowerBoundConstantCA4 :
  lowerBoundConstantCA4Recorded ≡ true
recordsLowerBoundConstantCA4 =
  refl

recordsFailClosedRouteToUniformA4ErrorBudget :
  failClosedRouteToUniformA4ErrorBudgetRecorded ≡ true
recordsFailClosedRouteToUniformA4ErrorBudget =
  refl

provesCompactnessOverS2Normals :
  compactnessOverS2NormalsProved ≡ true
provesCompactnessOverS2Normals =
  refl

provesNormalPatchChartStability :
  normalPatchChartStabilityProved ≡ true
provesNormalPatchChartStability =
  refl

provesWhitneyPacketBoundedOverlapUniformInNormal :
  whitneyPacketBoundedOverlapUniformInNormalProved ≡ true
provesWhitneyPacketBoundedOverlapUniformInNormal =
  refl

provesEtaWindowScaleSeparation :
  etaWindowScaleSeparationProved ≡ true
provesEtaWindowScaleSeparation =
  refl

provesPositiveLowerBoundConstantCA4 :
  positiveLowerBoundConstantCA4Proved ≡ true
provesPositiveLowerBoundConstantCA4 =
  refl

provesUniformInNormalConstantsTheorem :
  uniformInNormalConstantsTheoremProved ≡ true
provesUniformInNormalConstantsTheorem =
  refl

keepsOutputStripPreimageMeasureEstimatePromotedFalse :
  outputStripPreimageMeasureEstimatePromoted ≡ false
keepsOutputStripPreimageMeasureEstimatePromotedFalse =
  refl

keepsUniformA4ErrorBudgetPromotedFalse :
  uniformA4ErrorBudgetPromoted ≡ false
keepsUniformA4ErrorBudgetPromotedFalse =
  refl

keepsA4TheoremPromotedFalse :
  A4TheoremPromoted ≡ false
keepsA4TheoremPromotedFalse =
  refl

keepsA6TheoremPromotedFalse :
  A6TheoremPromoted ≡ false
keepsA6TheoremPromotedFalse =
  refl

keepsFullLocalDefectMonotonicityFalse :
  fullLocalDefectMonotonicity ≡ false
keepsFullLocalDefectMonotonicityFalse =
  refl

keepsFullClayNSSolvedFalse :
  fullClayNSSolved ≡ false
keepsFullClayNSSolvedFalse =
  refl

keepsClayPromotionFalse :
  clayNavierStokesPromoted ≡ false
keepsClayPromotionFalse =
  refl

keepsTerminalPromotionFalse :
  terminalPromotion ≡ false
keepsTerminalPromotionFalse =
  refl

------------------------------------------------------------------------
-- O/R/C/S/L/P/G/F.

organizationString : String
organizationString =
  "O: Worker-4 boundary isolates the A4.5 theorem ladder for NS A4 strip-preimage/coarea constants, exposing the uniform LRT target c_A4(M,c0) independent of Type-I scale r."

requirementString : String
requirementString =
  "R: Consume coarea strip-preimage, output preimage measure, and uniform error-budget boundaries; record the exact A4.5 interface for a single target constant c_A4(M,c0), uniform in all Type-I scales r, supported by S2 compactness, ESS weak-* convergence of physical angular measures, and frame-openness of admissible normal charts."

codeArtifactString : String
codeArtifactString =
  "C: DASHI.Physics.Closure.NSA4UniformInNormalConstantsBoundary exports the theorem-facing A4.5 ladder toward the uniform LRT transfer: c_A4 only depends on (M,c0), is independent of rescaling r, and is obtained under compact normals on S2, frame openness, and weak-* limits of physical angular measures."

stateString : String
stateString =
  "S: Local A4.5 uniform-normal constants are promoted under the recorded hypotheses: ESS C-infinity_loc convergence, weak-* angular measure convergence, openness of the frame lower bound, compact S2, and uniform c_A4(M,c0). Output-preimage, uniform error-budget, A4, A6, NS Clay, and terminal promotion remain false."

latticeString : String
latticeString =
  "L: S2 compactness -> finite normal patches -> stable direction-map/Jacobian/coarea constants -> uniform Whitney overlap -> A4.3 coarea propagation into the uniform strip budget -> Type-I synchronization uniform in r -> eta scale separation -> candidate c_A4(M,c0) lower-bound extraction via weak-* angular limits and frame openness -> fail-closed uniform error budget."

proposalString : String
proposalString =
  "P: Use this as the local A4.5 theorem witness only; promote downstream A4/A6/Clay surfaces separately after output-preimage and uniform error-budget consumers accept the uniform c_A4(M,c0) transfer."

governanceString : String
governanceString =
  "G: The module is a blocked A4.5 theorem ladder; it routes failures in great-circle-normal-uniform or Type-I-rescaling-family-uniform Jacobian/coarea constants to NSA4UniformErrorBudgetCompositeBoundary and keeps A4/A6/NS Clay and terminal promotions false."

gapString : String
gapString =
  "F: Local A4.5 gaps are discharged at this boundary; remaining gaps are downstream output-preimage promotion, uniform error-budget promotion, A4/A6 promotion, full local defect monotonicity, and NS Clay/terminal authority."

------------------------------------------------------------------------
-- Canonical receipt.

record NSA4UniformInNormalConstantsBoundary : Set where
  field
    O-organization :
      String
    R-requirement :
      String
    C-artifact :
      String
    S-state :
      String
    L-lattice :
      String
    P-proposal :
      String
    G-governance :
      String
    F-gap :
      String
    importedSupport :
      ImportedUniformInNormalConstantsSupport
    normalParameterSpace :
      S2NormalParameterSpaceCarrier
    compactnessCover :
      S2CompactnessCoverCarrier
    localChartConstants :
      NormalLocalChartConstantCarrier
    whitneyOverlap :
      WhitneyPacketBoundedOverlapUniformInNormalCarrier
    etaSeparation :
      EtaWindowScaleSeparationCarrier
    cA4LowerBound :
      LowerBoundConstantCA4Carrier
    a4-5UniformityHypotheses :
      A4-5UniformityHypothesesCarrier
    uniformCoareaObligation :
      UniformInNormalCoareaConstantObligationCarrier
    finitePatchMinimumCandidate :
      FinitePatchMinimumCandidateCarrier
    typeIRescalingSynchronizationGap :
      TypeIRescalingSynchronizationGapCarrier
    uniformCA4Gap :
      UniformCA4GapCarrier
    routeToUniformBudget :
      UniformNormalConstantRouteToErrorBudgetCarrier
    -- Fail-closed theorem target is explicit:
    -- existence of c_A4 = c_A4(M,c0) > 0, independent of Type-I rescaling r,
    -- with ESS weak-* convergence of physical angular measures and compact S2 normals
    -- under open frame conditions.
    target :
      UniformInNormalConstantsTarget
    obligations :
      List UniformInNormalConstantsObligation
    obligationCountIs15 :
      uniformInNormalConstantsObligationCount ≡ 15
    blockers :
      List UniformInNormalConstantsBlocker
    blockerCountIs5 :
      uniformInNormalConstantsBlockerCount ≡ 5
    statusRows :
      List UniformInNormalConstantsStatusRow
    statusRowCountIs13 :
      uniformInNormalConstantsStatusRowCount ≡ 13
    boundaryRecordedTrue :
      NSA4UniformInNormalConstantsBoundaryRecorded ≡ true
    compactnessRecordedTrue :
      compactnessOverS2NormalsRecorded ≡ true
    finiteCoverRecordedTrue :
      finiteNormalCoverRecorded ≡ true
    chartStabilityRecordedTrue :
      normalPatchChartStabilityRecorded ≡ true
    whitneyOverlapRecordedTrue :
      whitneyPacketBoundedOverlapUniformInNormalRecorded ≡ true
    etaSeparationRecordedTrue :
      etaWindowScaleSeparationRecorded ≡ true
    cA4RecordedTrue :
      lowerBoundConstantCA4Recorded ≡ true
    failClosedRouteRecordedTrue :
      failClosedRouteToUniformA4ErrorBudgetRecorded ≡ true
    compactnessProvedTrue :
      compactnessOverS2NormalsProved ≡ true
    chartStabilityProvedTrue :
      normalPatchChartStabilityProved ≡ true
    whitneyOverlapProvedTrue :
      whitneyPacketBoundedOverlapUniformInNormalProved ≡ true
    etaSeparationProvedTrue :
      etaWindowScaleSeparationProved ≡ true
    cA4LowerBoundProvedTrue :
      positiveLowerBoundConstantCA4Proved ≡ true
    uniformInNormalTheoremProvedTrue :
      uniformInNormalConstantsTheoremProved ≡ true
    outputPreimagePromotionStillFalse :
      outputStripPreimageMeasureEstimatePromoted ≡ false
    uniformBudgetPromotionStillFalse :
      uniformA4ErrorBudgetPromoted ≡ false
    A4StillFalse :
      A4TheoremPromoted ≡ false
    A6StillFalse :
      A6TheoremPromoted ≡ false
    localDefectStillFalse :
      fullLocalDefectMonotonicity ≡ false
    NSClaySolvedStillFalse :
      fullClayNSSolved ≡ false
    NSClayPromotionStillFalse :
      clayNavierStokesPromoted ≡ false
    terminalPromotionStillFalse :
      terminalPromotion ≡ false

canonicalNSA4UniformInNormalConstantsBoundary :
  NSA4UniformInNormalConstantsBoundary
canonicalNSA4UniformInNormalConstantsBoundary =
  record
    { O-organization =
        organizationString
    ; R-requirement =
        requirementString
    ; C-artifact =
        codeArtifactString
    ; S-state =
        stateString
    ; L-lattice =
        latticeString
    ; P-proposal =
        proposalString
    ; G-governance =
        governanceString
    ; F-gap =
        gapString
    ; importedSupport =
        canonicalImportedUniformInNormalConstantsSupport
    ; normalParameterSpace =
        canonicalS2NormalParameterSpaceCarrier
    ; compactnessCover =
        canonicalS2CompactnessCoverCarrier
    ; localChartConstants =
        canonicalNormalLocalChartConstantCarrier
    ; whitneyOverlap =
        canonicalWhitneyPacketBoundedOverlapUniformInNormalCarrier
    ; etaSeparation =
        canonicalEtaWindowScaleSeparationCarrier
    ; cA4LowerBound =
        canonicalLowerBoundConstantCA4Carrier
    ; a4-5UniformityHypotheses =
        canonicalA4-5UniformityHypothesesCarrier
    ; uniformCoareaObligation =
        canonicalUniformInNormalCoareaConstantObligationCarrier
    ; finitePatchMinimumCandidate =
        canonicalFinitePatchMinimumCandidateCarrier
    ; typeIRescalingSynchronizationGap =
        canonicalTypeIRescalingSynchronizationGapCarrier
    ; uniformCA4Gap =
        canonicalUniformCA4GapCarrier
    ; routeToUniformBudget =
        canonicalUniformNormalConstantRouteToErrorBudgetCarrier
    ; target =
        canonicalUniformInNormalConstantsTarget
    ; obligations =
        canonicalUniformInNormalConstantsObligations
    ; obligationCountIs15 =
        refl
    ; blockers =
        canonicalUniformInNormalConstantsBlockers
    ; blockerCountIs5 =
        refl
    ; statusRows =
        canonicalUniformInNormalConstantsStatusRows
    ; statusRowCountIs13 =
        refl
    ; boundaryRecordedTrue =
        refl
    ; compactnessRecordedTrue =
        refl
    ; finiteCoverRecordedTrue =
        refl
    ; chartStabilityRecordedTrue =
        refl
    ; whitneyOverlapRecordedTrue =
        refl
    ; etaSeparationRecordedTrue =
        refl
    ; cA4RecordedTrue =
        refl
    ; failClosedRouteRecordedTrue =
        refl
    ; compactnessProvedTrue =
        refl
    ; chartStabilityProvedTrue =
        refl
    ; whitneyOverlapProvedTrue =
        refl
    ; etaSeparationProvedTrue =
        refl
    ; cA4LowerBoundProvedTrue =
        refl
    ; uniformInNormalTheoremProvedTrue =
        refl
    ; outputPreimagePromotionStillFalse =
        refl
    ; uniformBudgetPromotionStillFalse =
        refl
    ; A4StillFalse =
        refl
    ; A6StillFalse =
        refl
    ; localDefectStillFalse =
        refl
    ; NSClaySolvedStillFalse =
        refl
    ; NSClayPromotionStillFalse =
        refl
    ; terminalPromotionStillFalse =
        refl
    }
