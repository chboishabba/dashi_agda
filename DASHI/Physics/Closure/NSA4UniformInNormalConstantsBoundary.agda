module DASHI.Physics.Closure.NSA4UniformInNormalConstantsBoundary where

-- NS A4 boundary: uniform-in-great-circle-normal constants for the
-- strip-preimage/coarea estimate.
--
-- This module records the missing analytic obligation that the constants
-- in the A4 eta-strip preimage/coarea estimate are uniform as the output
-- great-circle normal n ranges over S2.  The intended route is:
--
--   compact S2 normal cover
--     -> stable chart/Whitney packet constants
--     -> bounded packet overlap independent of n
--     -> eta-window scale separation from packet and antipodal scales
--     -> positive lower-bound constant c_A4
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
    outputPreimageEstimateStillFalse :
      OutputPreimage.OutputStripPreimageMeasureEstimateProved ≡ false
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
    ; outputPreimageEstimateStillFalse =
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

data UniformInNormalCoareaConstantObligationCarrier : Set where
  coareaStripConstantsUniformForAllGreatCircleNormals :
    Coarea.UniformInNormalConstantCarrier →
    Coarea.EtaStripCoareaSlabEstimateCarrier →
    LowerBoundConstantCA4Carrier →
    UniformInNormalCoareaConstantObligationCarrier

data UniformNormalConstantRouteToErrorBudgetCarrier : Set where
  routeUniformNormalConstantFailureIntoUniformA4ErrorBudget :
    UniformInNormalCoareaConstantObligationCarrier →
    OutputPreimage.A4OutputStripPreimageEstimateConsumer →
    UniformBudget.UniformA4ErrorSubtractionLedger →
    UniformBudget.UniformA4FailClosedTheoremCarrier →
    UniformNormalConstantRouteToErrorBudgetCarrier

data UniformInNormalConstantsTarget : Set where
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

canonicalUniformInNormalCoareaConstantObligationCarrier :
  UniformInNormalCoareaConstantObligationCarrier
canonicalUniformInNormalCoareaConstantObligationCarrier =
  coareaStripConstantsUniformForAllGreatCircleNormals
    Coarea.canonicalUniformInNormalConstantCarrier
    Coarea.canonicalEtaStripCoareaSlabEstimateCarrier
    canonicalLowerBoundConstantCA4Carrier

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
  quantifyGreatCircleNormalsByCompactS2 :
    UniformInNormalConstantsObligation
  extractFiniteNormalCoverWithStableCharts :
    UniformInNormalConstantsObligation
  proveChartJacobianConstantsStableOnNormalPatches :
    UniformInNormalConstantsObligation
  proveWhitneyPacketBoundedOverlapUniformInNormal :
    UniformInNormalConstantsObligation
  proveEtaWindowScaleSeparation :
    UniformInNormalConstantsObligation
  choosePositiveLowerBoundConstantCA4 :
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
  ∷ quantifyGreatCircleNormalsByCompactS2
  ∷ extractFiniteNormalCoverWithStableCharts
  ∷ proveChartJacobianConstantsStableOnNormalPatches
  ∷ proveWhitneyPacketBoundedOverlapUniformInNormal
  ∷ proveEtaWindowScaleSeparation
  ∷ choosePositiveLowerBoundConstantCA4
  ∷ routeFailureClosedToUniformA4ErrorBudget
  ∷ keepA4A6NSClayAndTerminalPromotionsFalse
  ∷ []

uniformInNormalConstantsObligationCount : Nat
uniformInNormalConstantsObligationCount =
  listLength canonicalUniformInNormalConstantsObligations

uniformInNormalConstantsObligationCountIs11 :
  uniformInNormalConstantsObligationCount ≡ 11
uniformInNormalConstantsObligationCountIs11 =
  refl

data UniformInNormalConstantsBlocker : Set where
  missingS2CompactnessCoverProof :
    UniformInNormalConstantsBlocker
  missingNormalPatchChartStabilityProof :
    UniformInNormalConstantsBlocker
  missingUniformWhitneyPacketBoundedOverlapProof :
    UniformInNormalConstantsBlocker
  missingEtaWindowScaleSeparationProof :
    UniformInNormalConstantsBlocker
  missingPositiveCA4LowerBoundProof :
    UniformInNormalConstantsBlocker
  missingUniformCoareaConstantTheorem :
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
  missingS2CompactnessCoverProof
  ∷ missingNormalPatchChartStabilityProof
  ∷ missingUniformWhitneyPacketBoundedOverlapProof
  ∷ missingEtaWindowScaleSeparationProof
  ∷ missingPositiveCA4LowerBoundProof
  ∷ missingUniformCoareaConstantTheorem
  ∷ missingOutputPreimagePromotion
  ∷ missingUniformErrorBudgetPromotion
  ∷ missingA4Promotion
  ∷ missingA6Promotion
  ∷ missingNavierStokesClayPromotion
  ∷ []

uniformInNormalConstantsBlockerCount : Nat
uniformInNormalConstantsBlockerCount =
  listLength canonicalUniformInNormalConstantsBlockers

uniformInNormalConstantsBlockerCountIs11 :
  uniformInNormalConstantsBlockerCount ≡ 11
uniformInNormalConstantsBlockerCountIs11 =
  refl

data UniformInNormalConstantsStatusRow : Set where
  boundaryRecordedStatus :
    UniformInNormalConstantsStatusRow
  threeRequestedBoundaryInputsConsumedStatus :
    UniformInNormalConstantsStatusRow
  compactnessOverS2NormalRecordedStatus :
    UniformInNormalConstantsStatusRow
  finiteNormalCoverRecordedStatus :
    UniformInNormalConstantsStatusRow
  whitneyPacketBoundedOverlapRecordedStatus :
    UniformInNormalConstantsStatusRow
  etaWindowScaleSeparationRecordedStatus :
    UniformInNormalConstantsStatusRow
  cA4LowerBoundConstantRecordedStatus :
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
  ∷ compactnessOverS2NormalRecordedStatus
  ∷ finiteNormalCoverRecordedStatus
  ∷ whitneyPacketBoundedOverlapRecordedStatus
  ∷ etaWindowScaleSeparationRecordedStatus
  ∷ cA4LowerBoundConstantRecordedStatus
  ∷ failClosedRouteToUniformErrorBudgetRecordedStatus
  ∷ A4AndNSClayRemainFalseStatus
  ∷ []

uniformInNormalConstantsStatusRowCount : Nat
uniformInNormalConstantsStatusRowCount =
  listLength canonicalUniformInNormalConstantsStatusRows

uniformInNormalConstantsStatusRowCountIs9 :
  uniformInNormalConstantsStatusRowCount ≡ 9
uniformInNormalConstantsStatusRowCountIs9 =
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
  false

normalPatchChartStabilityProved : Bool
normalPatchChartStabilityProved =
  false

whitneyPacketBoundedOverlapUniformInNormalProved : Bool
whitneyPacketBoundedOverlapUniformInNormalProved =
  false

etaWindowScaleSeparationProved : Bool
etaWindowScaleSeparationProved =
  false

positiveLowerBoundConstantCA4Proved : Bool
positiveLowerBoundConstantCA4Proved =
  false

uniformInNormalConstantsTheoremProved : Bool
uniformInNormalConstantsTheoremProved =
  false

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

keepsCompactnessOverS2NormalsFalse :
  compactnessOverS2NormalsProved ≡ false
keepsCompactnessOverS2NormalsFalse =
  refl

keepsNormalPatchChartStabilityFalse :
  normalPatchChartStabilityProved ≡ false
keepsNormalPatchChartStabilityFalse =
  refl

keepsWhitneyPacketBoundedOverlapUniformInNormalFalse :
  whitneyPacketBoundedOverlapUniformInNormalProved ≡ false
keepsWhitneyPacketBoundedOverlapUniformInNormalFalse =
  refl

keepsEtaWindowScaleSeparationFalse :
  etaWindowScaleSeparationProved ≡ false
keepsEtaWindowScaleSeparationFalse =
  refl

keepsPositiveLowerBoundConstantCA4False :
  positiveLowerBoundConstantCA4Proved ≡ false
keepsPositiveLowerBoundConstantCA4False =
  refl

keepsUniformInNormalConstantsTheoremFalse :
  uniformInNormalConstantsTheoremProved ≡ false
keepsUniformInNormalConstantsTheoremFalse =
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
  "O: Worker-2 boundary isolates the uniform-in-great-circle-normal constant obligation for the NS A4 strip-preimage/coarea estimate."

requirementString : String
requirementString =
  "R: Consume coarea strip-preimage, output preimage measure, and uniform error-budget boundaries; record compactness over n in S2, Whitney packet bounded overlap, eta-window scale separation, c_A4, and fail-closed error-budget routing."

codeArtifactString : String
codeArtifactString =
  "C: DASHI.Physics.Closure.NSA4UniformInNormalConstantsBoundary exports imported support, uniform-normal carriers, target, obligations, blockers, status rows, and false-promotion witnesses."

stateString : String
stateString =
  "S: Boundary facts are recorded only; compactness extraction, uniform overlap, eta separation, c_A4 positivity, output-preimage promotion, A4, A6, NS Clay, and terminal promotion remain false."

latticeString : String
latticeString =
  "L: S2 normal compactness -> finite normal patches -> stable chart constants -> uniform Whitney overlap -> eta scale separation -> c_A4 lower bound -> fail-closed uniform error budget."

proposalString : String
proposalString =
  "P: Promote only after proving the finite S2 cover, stable packet constants, normal-independent overlap summation, eta scale separation, and positive c_A4 lower bound quantitatively."

governanceString : String
governanceString =
  "G: The module is a boundary ledger; it routes missing uniformity to NSA4UniformErrorBudgetCompositeBoundary and keeps A4/NS Clay false."

gapString : String
gapString =
  "F: Open gaps are S2 compactness cover proof, normal-patch chart stability, uniform Whitney bounded overlap, eta-window separation, positive c_A4 proof, and downstream A4/A6/Clay promotion."

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
    uniformCoareaObligation :
      UniformInNormalCoareaConstantObligationCarrier
    routeToUniformBudget :
      UniformNormalConstantRouteToErrorBudgetCarrier
    target :
      UniformInNormalConstantsTarget
    obligations :
      List UniformInNormalConstantsObligation
    obligationCountIs11 :
      uniformInNormalConstantsObligationCount ≡ 11
    blockers :
      List UniformInNormalConstantsBlocker
    blockerCountIs11 :
      uniformInNormalConstantsBlockerCount ≡ 11
    statusRows :
      List UniformInNormalConstantsStatusRow
    statusRowCountIs9 :
      uniformInNormalConstantsStatusRowCount ≡ 9
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
    compactnessStillFalse :
      compactnessOverS2NormalsProved ≡ false
    chartStabilityStillFalse :
      normalPatchChartStabilityProved ≡ false
    whitneyOverlapStillFalse :
      whitneyPacketBoundedOverlapUniformInNormalProved ≡ false
    etaSeparationStillFalse :
      etaWindowScaleSeparationProved ≡ false
    cA4LowerBoundStillFalse :
      positiveLowerBoundConstantCA4Proved ≡ false
    uniformInNormalTheoremStillFalse :
      uniformInNormalConstantsTheoremProved ≡ false
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
    ; uniformCoareaObligation =
        canonicalUniformInNormalCoareaConstantObligationCarrier
    ; routeToUniformBudget =
        canonicalUniformNormalConstantRouteToErrorBudgetCarrier
    ; target =
        canonicalUniformInNormalConstantsTarget
    ; obligations =
        canonicalUniformInNormalConstantsObligations
    ; obligationCountIs11 =
        refl
    ; blockers =
        canonicalUniformInNormalConstantsBlockers
    ; blockerCountIs11 =
        refl
    ; statusRows =
        canonicalUniformInNormalConstantsStatusRows
    ; statusRowCountIs9 =
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
    ; compactnessStillFalse =
        refl
    ; chartStabilityStillFalse =
        refl
    ; whitneyOverlapStillFalse =
        refl
    ; etaSeparationStillFalse =
        refl
    ; cA4LowerBoundStillFalse =
        refl
    ; uniformInNormalTheoremStillFalse =
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
