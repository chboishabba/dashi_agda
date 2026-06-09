module DASHI.Physics.Closure.NSOutputStripPreimageMeasureEstimateBoundary where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; []; _∷_)

import DASHI.Physics.Closure.NSAntipodalTubeNullMassBoundary
  as Antipodal
import DASHI.Physics.Closure.NSOutputGreatCircleStripSlicingBoundary
  as OutputStrip
import DASHI.Physics.Closure.NSPhiJacobianLowerBoundBoundary
  as PhiJacobian
import DASHI.Physics.Closure.NSSardRegularValueSlicingBoundary
  as Sard
import DASHI.Physics.Closure.NSWhitneyFubiniDisintegrationBoundary
  as Fubini

------------------------------------------------------------------------
-- NS A4 output strip preimage measure estimate boundary.
--
-- This boundary records the composite A4 estimate for the map
--
--   Phi(theta1,theta2) = normalize(theta1 + theta2)
--
-- and a regular output great-circle strip.  The intended theorem is that
-- the product/angular measure of the Phi-preimage of an eta-neighborhood
-- of a great circle is controlled by the output strip width, the local
-- lower Jacobian bound, Whitney packet bounded overlap, and the null
-- budgets for antipodal, rank-drop, critical-value, and packet-boundary
-- exceptional sets.
--
-- This file is a boundary/receipt module only.  It consumes the existing
-- A4 child surfaces when available, records the exact theorem statement
-- shape and promotion blockers, and keeps all theorem and promotion flags
-- fail-closed.  It does not prove Sard, Fubini disintegration, the
-- antipodal tube estimate, the Phi Jacobian lower bound, the output strip
-- slicing estimate, A4, or Navier-Stokes Clay.

listLength : {A : Set} → List A → Nat
listLength [] =
  zero
listLength (_ ∷ xs) =
  suc (listLength xs)

------------------------------------------------------------------------
-- Imported child surfaces.

record ImportedOutputStripPreimageMeasureSupport : Set where
  field
    outputGreatCircleStripSlicingBoundary :
      OutputStrip.NSOutputGreatCircleStripSlicingBoundary
    outputGreatCircleStripSlicingBoundaryIsCanonical :
      outputGreatCircleStripSlicingBoundary
        ≡ OutputStrip.canonicalNSOutputGreatCircleStripSlicingBoundary
    phiJacobianLowerBoundBoundary :
      PhiJacobian.NSPhiJacobianLowerBoundBoundary
    phiJacobianLowerBoundBoundaryIsCanonical :
      phiJacobianLowerBoundBoundary
        ≡ PhiJacobian.canonicalNSPhiJacobianLowerBoundBoundary
    whitneyFubiniDisintegrationBoundary :
      Fubini.NSWhitneyFubiniDisintegrationBoundary
    whitneyFubiniDisintegrationBoundaryIsCanonical :
      whitneyFubiniDisintegrationBoundary
        ≡ Fubini.canonicalNSWhitneyFubiniDisintegrationBoundary
    antipodalTubeNullMassBoundary :
      Antipodal.NSAntipodalTubeNullMassBoundary
    antipodalTubeNullMassBoundaryIsCanonical :
      antipodalTubeNullMassBoundary
        ≡ Antipodal.canonicalNSAntipodalTubeNullMassBoundary
    sardRegularValueSlicingBoundary :
      Sard.NSSardRegularValueSlicingBoundary
    sardRegularValueSlicingBoundaryIsCanonical :
      sardRegularValueSlicingBoundary
        ≡ Sard.canonicalNSSardRegularValueSlicingBoundary

    outputStripTarget :
      OutputStrip.OutputGreatCircleStripSlicingTarget
    outputStripTargetIsCanonical :
      outputStripTarget
        ≡ OutputStrip.canonicalOutputGreatCircleStripSlicingTarget
    outputStripPreimageSlice :
      OutputStrip.PhiPreimageStripSliceCarrier
    outputStripPreimageSliceIsCanonical :
      outputStripPreimageSlice
        ≡ OutputStrip.canonicalPhiPreimageStripSliceCarrier
    outputStripMeasureEstimate :
      OutputStrip.StripPreimageMeasureEstimateCarrier
    outputStripMeasureEstimateIsCanonical :
      outputStripMeasureEstimate
        ≡ OutputStrip.canonicalStripPreimageMeasureEstimateCarrier
    phiJacobianLowerBound :
      PhiJacobian.PhiJacobianLowerBoundCarrier
    phiJacobianLowerBoundIsCanonical :
      phiJacobianLowerBound
        ≡ PhiJacobian.canonicalPhiJacobianLowerBoundCarrier
    phiOutputStripWidthRelation :
      PhiJacobian.OutputStripWidthRelationCarrier
    phiOutputStripWidthRelationIsCanonical :
      phiOutputStripWidthRelation
        ≡ PhiJacobian.canonicalOutputStripWidthRelationCarrier
    whitneyFubiniTarget :
      Fubini.WhitneyFubiniDisintegrationTarget
    whitneyFubiniTargetIsCanonical :
      whitneyFubiniTarget
        ≡ Fubini.canonicalWhitneyFubiniDisintegrationTarget
    fubiniExceptionalRouting :
      Fubini.ExceptionalNullSetRoutingCarrier
    fubiniExceptionalRoutingIsCanonical :
      fubiniExceptionalRouting
        ≡ Fubini.canonicalExceptionalNullSetRoutingCarrier
    antipodalNullMassTarget :
      Antipodal.AntipodalTubeNullMassTarget
    antipodalNullMassTargetIsCanonical :
      antipodalNullMassTarget
        ≡ Antipodal.canonicalAntipodalTubeNullMassTarget
    sardRegularValueTarget :
      Sard.SardRegularValueSlicingTarget
    sardRegularValueTargetIsCanonical :
      sardRegularValueTarget
        ≡ Sard.canonicalSardRegularValueSlicingTarget

    childOutputStripStillFalse :
      OutputStrip.OutputGreatCircleStripSlicingProved ≡ false
    childPreimageMeasureStillFalse :
      OutputStrip.preimageMeasureEstimateProved ≡ false
    childPhiJacobianStillFalse :
      PhiJacobian.PhiJacobianLowerBoundTheoremProved ≡ false
    childFubiniStillFalse :
      Fubini.WhitneyFubiniDisintegrationProved ≡ false
    childAntipodalStillFalse :
      Antipodal.antipodalTubeNullMassProved ≡ false
    childSardStillFalse :
      Sard.SardRegularValueSlicingProved ≡ false

canonicalImportedOutputStripPreimageMeasureSupport :
  ImportedOutputStripPreimageMeasureSupport
canonicalImportedOutputStripPreimageMeasureSupport =
  record
    { outputGreatCircleStripSlicingBoundary =
        OutputStrip.canonicalNSOutputGreatCircleStripSlicingBoundary
    ; outputGreatCircleStripSlicingBoundaryIsCanonical =
        refl
    ; phiJacobianLowerBoundBoundary =
        PhiJacobian.canonicalNSPhiJacobianLowerBoundBoundary
    ; phiJacobianLowerBoundBoundaryIsCanonical =
        refl
    ; whitneyFubiniDisintegrationBoundary =
        Fubini.canonicalNSWhitneyFubiniDisintegrationBoundary
    ; whitneyFubiniDisintegrationBoundaryIsCanonical =
        refl
    ; antipodalTubeNullMassBoundary =
        Antipodal.canonicalNSAntipodalTubeNullMassBoundary
    ; antipodalTubeNullMassBoundaryIsCanonical =
        refl
    ; sardRegularValueSlicingBoundary =
        Sard.canonicalNSSardRegularValueSlicingBoundary
    ; sardRegularValueSlicingBoundaryIsCanonical =
        refl
    ; outputStripTarget =
        OutputStrip.canonicalOutputGreatCircleStripSlicingTarget
    ; outputStripTargetIsCanonical =
        refl
    ; outputStripPreimageSlice =
        OutputStrip.canonicalPhiPreimageStripSliceCarrier
    ; outputStripPreimageSliceIsCanonical =
        refl
    ; outputStripMeasureEstimate =
        OutputStrip.canonicalStripPreimageMeasureEstimateCarrier
    ; outputStripMeasureEstimateIsCanonical =
        refl
    ; phiJacobianLowerBound =
        PhiJacobian.canonicalPhiJacobianLowerBoundCarrier
    ; phiJacobianLowerBoundIsCanonical =
        refl
    ; phiOutputStripWidthRelation =
        PhiJacobian.canonicalOutputStripWidthRelationCarrier
    ; phiOutputStripWidthRelationIsCanonical =
        refl
    ; whitneyFubiniTarget =
        Fubini.canonicalWhitneyFubiniDisintegrationTarget
    ; whitneyFubiniTargetIsCanonical =
        refl
    ; fubiniExceptionalRouting =
        Fubini.canonicalExceptionalNullSetRoutingCarrier
    ; fubiniExceptionalRoutingIsCanonical =
        refl
    ; antipodalNullMassTarget =
        Antipodal.canonicalAntipodalTubeNullMassTarget
    ; antipodalNullMassTargetIsCanonical =
        refl
    ; sardRegularValueTarget =
        Sard.canonicalSardRegularValueSlicingTarget
    ; sardRegularValueTargetIsCanonical =
        refl
    ; childOutputStripStillFalse =
        refl
    ; childPreimageMeasureStillFalse =
        refl
    ; childPhiJacobianStillFalse =
        refl
    ; childFubiniStillFalse =
        refl
    ; childAntipodalStillFalse =
        refl
    ; childSardStillFalse =
        refl
    }

------------------------------------------------------------------------
-- Composite estimate carriers.

data OutputGreatCircleStripTestCarrier : Set where
  regularGreatCircleStripTestForPhiOutput :
    OutputStrip.GreatCircleCarrier →
    OutputStrip.OutputStripWidthCarrier →
    Sard.OutputGreatCircleStripCarrier →
    OutputGreatCircleStripTestCarrier

data PhiNormalizeSumPreimageCarrier : Set where
  preimageOfGreatCircleStripUnderNormalizeThetaSum :
    OutputGreatCircleStripTestCarrier →
    OutputStrip.PhiPreimageStripSliceCarrier →
    PhiJacobian.PhiDerivativeFormulaCarrier →
    Antipodal.NormalizeSumDomainExclusion →
    PhiNormalizeSumPreimageCarrier

data PreimageMeasureDomainCarrier : Set where
  productAngularDomainMinusAntipodalCriticalAndBoundaryNullSets :
    PhiNormalizeSumPreimageCarrier →
    Antipodal.AntipodalTubeCarrier →
    Sard.CriticalSetAwayFromAntipodalCarrier →
    Fubini.ExceptionalNullSetRoutingCarrier →
    PreimageMeasureDomainCarrier

data StripWidthJacobianBudgetCarrier : Set where
  stripWidthDividedByUniformPhiJacobianLowerBound :
    PhiJacobian.PhiJacobianLowerBoundCarrier →
    PhiJacobian.OutputStripWidthRelationCarrier →
    PhiJacobian.WhitneyCapUniformConstantCarrier →
    StripWidthJacobianBudgetCarrier

data WhitneyPacketDisintegratedPreimageCarrier : Set where
  preimageMeasuredAfterWhitneyFubiniPacketDisintegration :
    PreimageMeasureDomainCarrier →
    Fubini.PhysicalPacketDisintegrationCarrier →
    Fubini.FourierOutputPacketDisintegrationCarrier →
    OutputStrip.WhitneyCapStripSlicingCarrier →
    WhitneyPacketDisintegratedPreimageCarrier

data NullExceptionalBudgetCarrier : Set where
  antipodalCriticalRankDropAndPacketBoundarySetsHaveNullBudget :
    Antipodal.AntipodalTubeNullMassTarget →
    Sard.SardExceptionalSetCarrier →
    PhiJacobian.DegenerateTriadBudgetAbsorptionCarrier →
    Fubini.ExceptionalNullSetRoutingCarrier →
    OutputStrip.StripExceptionalSetRoutingCarrier →
    NullExceptionalBudgetCarrier

data OutputStripPreimageMeasureEstimateCarrier : Set where
  etaStripPreimageMeasureControlledByJacobianFubiniAndNullBudget :
    WhitneyPacketDisintegratedPreimageCarrier →
    StripWidthJacobianBudgetCarrier →
    NullExceptionalBudgetCarrier →
    OutputStrip.StripPreimageMeasureEstimateCarrier →
    OutputStrip.WhitneyLowerBoundTransferCarrier →
    OutputStripPreimageMeasureEstimateCarrier

data A4OutputStripPreimageEstimateConsumer : Set where
  feedsRegularGreatCircleStripEstimateIntoA4OutputSupport :
    OutputStripPreimageMeasureEstimateCarrier →
    Sard.StripSlicingEstimateCarrier →
    Fubini.OutputSupportLowerBoundConsumer →
    OutputStrip.NoCollapseConsumerCarrier →
    A4OutputStripPreimageEstimateConsumer

data OutputStripPreimageMeasureEstimateTarget : Set where
  PhiNormalizeSumGreatCircleStripPreimageHasFailClosedA4Estimate :
    OutputGreatCircleStripTestCarrier →
    PhiNormalizeSumPreimageCarrier →
    PreimageMeasureDomainCarrier →
    StripWidthJacobianBudgetCarrier →
    WhitneyPacketDisintegratedPreimageCarrier →
    NullExceptionalBudgetCarrier →
    OutputStripPreimageMeasureEstimateCarrier →
    A4OutputStripPreimageEstimateConsumer →
    OutputStrip.OutputGreatCircleStripSlicingTarget →
    OutputStripPreimageMeasureEstimateTarget

canonicalOutputGreatCircleStripTestCarrier :
  OutputGreatCircleStripTestCarrier
canonicalOutputGreatCircleStripTestCarrier =
  regularGreatCircleStripTestForPhiOutput
    OutputStrip.canonicalGreatCircleCarrier
    OutputStrip.canonicalOutputStripWidthCarrier
    Sard.canonicalOutputGreatCircleStripCarrier

canonicalPhiNormalizeSumPreimageCarrier :
  PhiNormalizeSumPreimageCarrier
canonicalPhiNormalizeSumPreimageCarrier =
  preimageOfGreatCircleStripUnderNormalizeThetaSum
    canonicalOutputGreatCircleStripTestCarrier
    OutputStrip.canonicalPhiPreimageStripSliceCarrier
    PhiJacobian.canonicalPhiDerivativeFormulaCarrier
    Antipodal.canonicalNormalizeSumDomainExclusion

canonicalPreimageMeasureDomainCarrier :
  PreimageMeasureDomainCarrier
canonicalPreimageMeasureDomainCarrier =
  productAngularDomainMinusAntipodalCriticalAndBoundaryNullSets
    canonicalPhiNormalizeSumPreimageCarrier
    Antipodal.canonicalAntipodalTubeCarrier
    Sard.canonicalCriticalSetAwayFromAntipodalCarrier
    Fubini.canonicalExceptionalNullSetRoutingCarrier

canonicalStripWidthJacobianBudgetCarrier :
  StripWidthJacobianBudgetCarrier
canonicalStripWidthJacobianBudgetCarrier =
  stripWidthDividedByUniformPhiJacobianLowerBound
    PhiJacobian.canonicalPhiJacobianLowerBoundCarrier
    PhiJacobian.canonicalOutputStripWidthRelationCarrier
    PhiJacobian.canonicalWhitneyCapUniformConstantCarrier

canonicalWhitneyPacketDisintegratedPreimageCarrier :
  WhitneyPacketDisintegratedPreimageCarrier
canonicalWhitneyPacketDisintegratedPreimageCarrier =
  preimageMeasuredAfterWhitneyFubiniPacketDisintegration
    canonicalPreimageMeasureDomainCarrier
    Fubini.canonicalPhysicalPacketDisintegrationCarrier
    Fubini.canonicalFourierOutputPacketDisintegrationCarrier
    OutputStrip.canonicalWhitneyCapStripSlicingCarrier

canonicalNullExceptionalBudgetCarrier :
  NullExceptionalBudgetCarrier
canonicalNullExceptionalBudgetCarrier =
  antipodalCriticalRankDropAndPacketBoundarySetsHaveNullBudget
    Antipodal.canonicalAntipodalTubeNullMassTarget
    Sard.canonicalSardExceptionalSetCarrier
    PhiJacobian.canonicalDegenerateTriadBudgetAbsorptionCarrier
    Fubini.canonicalExceptionalNullSetRoutingCarrier
    OutputStrip.canonicalStripExceptionalSetRoutingCarrier

canonicalOutputStripPreimageMeasureEstimateCarrier :
  OutputStripPreimageMeasureEstimateCarrier
canonicalOutputStripPreimageMeasureEstimateCarrier =
  etaStripPreimageMeasureControlledByJacobianFubiniAndNullBudget
    canonicalWhitneyPacketDisintegratedPreimageCarrier
    canonicalStripWidthJacobianBudgetCarrier
    canonicalNullExceptionalBudgetCarrier
    OutputStrip.canonicalStripPreimageMeasureEstimateCarrier
    OutputStrip.canonicalWhitneyLowerBoundTransferCarrier

canonicalA4OutputStripPreimageEstimateConsumer :
  A4OutputStripPreimageEstimateConsumer
canonicalA4OutputStripPreimageEstimateConsumer =
  feedsRegularGreatCircleStripEstimateIntoA4OutputSupport
    canonicalOutputStripPreimageMeasureEstimateCarrier
    Sard.canonicalStripSlicingEstimateCarrier
    Fubini.canonicalOutputSupportLowerBoundConsumer
    OutputStrip.canonicalNoCollapseConsumerCarrier

canonicalOutputStripPreimageMeasureEstimateTarget :
  OutputStripPreimageMeasureEstimateTarget
canonicalOutputStripPreimageMeasureEstimateTarget =
  PhiNormalizeSumGreatCircleStripPreimageHasFailClosedA4Estimate
    canonicalOutputGreatCircleStripTestCarrier
    canonicalPhiNormalizeSumPreimageCarrier
    canonicalPreimageMeasureDomainCarrier
    canonicalStripWidthJacobianBudgetCarrier
    canonicalWhitneyPacketDisintegratedPreimageCarrier
    canonicalNullExceptionalBudgetCarrier
    canonicalOutputStripPreimageMeasureEstimateCarrier
    canonicalA4OutputStripPreimageEstimateConsumer
    OutputStrip.canonicalOutputGreatCircleStripSlicingTarget

------------------------------------------------------------------------
-- Obligations, blockers, and status rows.

data OutputStripPreimageMeasureObligation : Set where
  fixRegularOutputGreatCircleAndEtaStrip :
    OutputStripPreimageMeasureObligation
  definePhiAsNormalizeThetaOnePlusThetaTwoOnTubeComplement :
    OutputStripPreimageMeasureObligation
  pullBackGreatCircleStripThroughPhi :
    OutputStripPreimageMeasureObligation
  restrictMeasureDomainAwayFromAntipodalTube :
    OutputStripPreimageMeasureObligation
  discardSardCriticalAndRankDropValues :
    OutputStripPreimageMeasureObligation
  disintegrateProductMeasureAcrossWhitneyPackets :
    OutputStripPreimageMeasureObligation
  applyUniformPhiJacobianLowerBoundOnEachPacket :
    OutputStripPreimageMeasureObligation
  compareOutputStripWidthWithInputPacketScale :
    OutputStripPreimageMeasureObligation
  sumPacketPreimageBoundsUsingBoundedOverlap :
    OutputStripPreimageMeasureObligation
  routePacketBoundaryLowVorticityAndAntipodalExceptions :
    OutputStripPreimageMeasureObligation
  feedPreimageEstimateIntoOutputGreatCircleStripSlicing :
    OutputStripPreimageMeasureObligation
  keepA4AndClayPromotionClosed :
    OutputStripPreimageMeasureObligation

canonicalOutputStripPreimageMeasureObligations :
  List OutputStripPreimageMeasureObligation
canonicalOutputStripPreimageMeasureObligations =
  fixRegularOutputGreatCircleAndEtaStrip
  ∷ definePhiAsNormalizeThetaOnePlusThetaTwoOnTubeComplement
  ∷ pullBackGreatCircleStripThroughPhi
  ∷ restrictMeasureDomainAwayFromAntipodalTube
  ∷ discardSardCriticalAndRankDropValues
  ∷ disintegrateProductMeasureAcrossWhitneyPackets
  ∷ applyUniformPhiJacobianLowerBoundOnEachPacket
  ∷ compareOutputStripWidthWithInputPacketScale
  ∷ sumPacketPreimageBoundsUsingBoundedOverlap
  ∷ routePacketBoundaryLowVorticityAndAntipodalExceptions
  ∷ feedPreimageEstimateIntoOutputGreatCircleStripSlicing
  ∷ keepA4AndClayPromotionClosed
  ∷ []

outputStripPreimageMeasureObligationCount : Nat
outputStripPreimageMeasureObligationCount =
  listLength canonicalOutputStripPreimageMeasureObligations

outputStripPreimageMeasureObligationCountIs12 :
  outputStripPreimageMeasureObligationCount ≡ 12
outputStripPreimageMeasureObligationCountIs12 =
  refl

data OutputStripPreimageMeasureBlocker : Set where
  missingAnalyticPreimageMeasureInequality :
    OutputStripPreimageMeasureBlocker
  missingPhiJacobianQuantitativeLowerBound :
    OutputStripPreimageMeasureBlocker
  missingAntipodalTubeNullMassEstimate :
    OutputStripPreimageMeasureBlocker
  missingSardCriticalValueNullSet :
    OutputStripPreimageMeasureBlocker
  missingWhitneyFubiniPacketDisintegration :
    OutputStripPreimageMeasureBlocker
  missingBoundedOverlapPacketSummation :
    OutputStripPreimageMeasureBlocker
  missingExceptionalSetRoutingProof :
    OutputStripPreimageMeasureBlocker
  missingOutputStripSlicingPromotion :
    OutputStripPreimageMeasureBlocker
  missingA4FourierOutputCouplingPromotion :
    OutputStripPreimageMeasureBlocker
  missingClayPromotion :
    OutputStripPreimageMeasureBlocker

canonicalOutputStripPreimageMeasureBlockers :
  List OutputStripPreimageMeasureBlocker
canonicalOutputStripPreimageMeasureBlockers =
  missingAnalyticPreimageMeasureInequality
  ∷ missingPhiJacobianQuantitativeLowerBound
  ∷ missingAntipodalTubeNullMassEstimate
  ∷ missingSardCriticalValueNullSet
  ∷ missingWhitneyFubiniPacketDisintegration
  ∷ missingBoundedOverlapPacketSummation
  ∷ missingExceptionalSetRoutingProof
  ∷ missingOutputStripSlicingPromotion
  ∷ missingA4FourierOutputCouplingPromotion
  ∷ missingClayPromotion
  ∷ []

outputStripPreimageMeasureBlockerCount : Nat
outputStripPreimageMeasureBlockerCount =
  listLength canonicalOutputStripPreimageMeasureBlockers

outputStripPreimageMeasureBlockerCountIs10 :
  outputStripPreimageMeasureBlockerCount ≡ 10
outputStripPreimageMeasureBlockerCountIs10 =
  refl

data OutputStripPreimageMeasureStatusRow : Set where
  boundaryRecordedStatus :
    OutputStripPreimageMeasureStatusRow
  childOutputStripSurfaceConsumedStatus :
    OutputStripPreimageMeasureStatusRow
  childPhiJacobianSurfaceConsumedStatus :
    OutputStripPreimageMeasureStatusRow
  childWhitneyFubiniSurfaceConsumedStatus :
    OutputStripPreimageMeasureStatusRow
  childAntipodalTubeSurfaceConsumedStatus :
    OutputStripPreimageMeasureStatusRow
  childSardRegularValueSurfaceConsumedStatus :
    OutputStripPreimageMeasureStatusRow
  PhiNormalizeSumPreimageCarrierRecordedStatus :
    OutputStripPreimageMeasureStatusRow
  stripWidthJacobianBudgetRecordedStatus :
    OutputStripPreimageMeasureStatusRow
  nullExceptionalBudgetRecordedStatus :
    OutputStripPreimageMeasureStatusRow
  theoremAndPromotionFlagsFailClosedStatus :
    OutputStripPreimageMeasureStatusRow

canonicalOutputStripPreimageMeasureStatusRows :
  List OutputStripPreimageMeasureStatusRow
canonicalOutputStripPreimageMeasureStatusRows =
  boundaryRecordedStatus
  ∷ childOutputStripSurfaceConsumedStatus
  ∷ childPhiJacobianSurfaceConsumedStatus
  ∷ childWhitneyFubiniSurfaceConsumedStatus
  ∷ childAntipodalTubeSurfaceConsumedStatus
  ∷ childSardRegularValueSurfaceConsumedStatus
  ∷ PhiNormalizeSumPreimageCarrierRecordedStatus
  ∷ stripWidthJacobianBudgetRecordedStatus
  ∷ nullExceptionalBudgetRecordedStatus
  ∷ theoremAndPromotionFlagsFailClosedStatus
  ∷ []

outputStripPreimageMeasureStatusRowCount : Nat
outputStripPreimageMeasureStatusRowCount =
  listLength canonicalOutputStripPreimageMeasureStatusRows

outputStripPreimageMeasureStatusRowCountIs10 :
  outputStripPreimageMeasureStatusRowCount ≡ 10
outputStripPreimageMeasureStatusRowCountIs10 =
  refl

------------------------------------------------------------------------
-- Promotion-closed type.

data OutputStripPreimageMeasurePromotion : Set where

outputStripPreimageMeasurePromotionImpossibleHere :
  OutputStripPreimageMeasurePromotion →
  ⊥
outputStripPreimageMeasurePromotionImpossibleHere ()

------------------------------------------------------------------------
-- Fail-closed governance flags.

NSOutputStripPreimageMeasureEstimateBoundaryRecorded : Bool
NSOutputStripPreimageMeasureEstimateBoundaryRecorded =
  true

PhiNormalizeSumMapRecorded : Bool
PhiNormalizeSumMapRecorded =
  true

outputGreatCircleStripTestRecorded : Bool
outputGreatCircleStripTestRecorded =
  true

PhiPreimageMeasureDomainRecorded : Bool
PhiPreimageMeasureDomainRecorded =
  true

stripWidthJacobianBudgetRecorded : Bool
stripWidthJacobianBudgetRecorded =
  true

WhitneyFubiniPreimageDisintegrationRecorded : Bool
WhitneyFubiniPreimageDisintegrationRecorded =
  true

nullExceptionalBudgetRecorded : Bool
nullExceptionalBudgetRecorded =
  true

outputStripPreimageEstimateCarrierRecorded : Bool
outputStripPreimageEstimateCarrierRecorded =
  true

analyticPreimageMeasureEstimateProved : Bool
analyticPreimageMeasureEstimateProved =
  false

PhiJacobianLowerBoundConsumedAsTheorem : Bool
PhiJacobianLowerBoundConsumedAsTheorem =
  false

WhitneyFubiniDisintegrationConsumedAsTheorem : Bool
WhitneyFubiniDisintegrationConsumedAsTheorem =
  false

antipodalTubeNullMassConsumedAsTheorem : Bool
antipodalTubeNullMassConsumedAsTheorem =
  false

SardRegularValueSlicingConsumedAsTheorem : Bool
SardRegularValueSlicingConsumedAsTheorem =
  false

OutputGreatCircleStripSlicingConsumedAsTheorem : Bool
OutputGreatCircleStripSlicingConsumedAsTheorem =
  false

OutputStripPreimageMeasureEstimateProved : Bool
OutputStripPreimageMeasureEstimateProved =
  false

A4WhitneyCouplingInequalityProved : Bool
A4WhitneyCouplingInequalityProved =
  false

A4LeiRenTianFourierOutputCouplingProved : Bool
A4LeiRenTianFourierOutputCouplingProved =
  false

triadicCompensatedLeakageIdentityProved : Bool
triadicCompensatedLeakageIdentityProved =
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
  NSOutputStripPreimageMeasureEstimateBoundaryRecorded ≡ true
recordsBoundary =
  refl

recordsPhiNormalizeSumMap :
  PhiNormalizeSumMapRecorded ≡ true
recordsPhiNormalizeSumMap =
  refl

recordsOutputGreatCircleStripTest :
  outputGreatCircleStripTestRecorded ≡ true
recordsOutputGreatCircleStripTest =
  refl

recordsPhiPreimageMeasureDomain :
  PhiPreimageMeasureDomainRecorded ≡ true
recordsPhiPreimageMeasureDomain =
  refl

recordsStripWidthJacobianBudget :
  stripWidthJacobianBudgetRecorded ≡ true
recordsStripWidthJacobianBudget =
  refl

recordsWhitneyFubiniPreimageDisintegration :
  WhitneyFubiniPreimageDisintegrationRecorded ≡ true
recordsWhitneyFubiniPreimageDisintegration =
  refl

recordsNullExceptionalBudget :
  nullExceptionalBudgetRecorded ≡ true
recordsNullExceptionalBudget =
  refl

recordsOutputStripPreimageEstimateCarrier :
  outputStripPreimageEstimateCarrierRecorded ≡ true
recordsOutputStripPreimageEstimateCarrier =
  refl

keepsAnalyticPreimageMeasureEstimateFalse :
  analyticPreimageMeasureEstimateProved ≡ false
keepsAnalyticPreimageMeasureEstimateFalse =
  refl

keepsPhiJacobianTheoremConsumptionFalse :
  PhiJacobianLowerBoundConsumedAsTheorem ≡ false
keepsPhiJacobianTheoremConsumptionFalse =
  refl

keepsWhitneyFubiniTheoremConsumptionFalse :
  WhitneyFubiniDisintegrationConsumedAsTheorem ≡ false
keepsWhitneyFubiniTheoremConsumptionFalse =
  refl

keepsAntipodalTubeTheoremConsumptionFalse :
  antipodalTubeNullMassConsumedAsTheorem ≡ false
keepsAntipodalTubeTheoremConsumptionFalse =
  refl

keepsSardRegularValueTheoremConsumptionFalse :
  SardRegularValueSlicingConsumedAsTheorem ≡ false
keepsSardRegularValueTheoremConsumptionFalse =
  refl

keepsOutputStripTheoremConsumptionFalse :
  OutputGreatCircleStripSlicingConsumedAsTheorem ≡ false
keepsOutputStripTheoremConsumptionFalse =
  refl

keepsOutputStripPreimageMeasureEstimateFalse :
  OutputStripPreimageMeasureEstimateProved ≡ false
keepsOutputStripPreimageMeasureEstimateFalse =
  refl

keepsA4WhitneyCouplingFalse :
  A4WhitneyCouplingInequalityProved ≡ false
keepsA4WhitneyCouplingFalse =
  refl

keepsA4LeiRenTianFourierOutputCouplingFalse :
  A4LeiRenTianFourierOutputCouplingProved ≡ false
keepsA4LeiRenTianFourierOutputCouplingFalse =
  refl

keepsTriadicCompensatedLeakageFalse :
  triadicCompensatedLeakageIdentityProved ≡ false
keepsTriadicCompensatedLeakageFalse =
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
  "O: NS A4 output-strip preimage estimate is isolated as the composite boundary over output strip slicing, Phi-Jacobian, Whitney/Fubini, antipodal null mass, and Sard regular-value slicing."

requirementString : String
requirementString =
  "R: Record the great-circle strip preimage estimate for Phi(theta1,theta2)=normalize(theta1+theta2), consuming child surfaces without promoting their open theorem flags."

codeArtifactString : String
codeArtifactString =
  "C: DASHI.Physics.Closure.NSOutputStripPreimageMeasureEstimateBoundary exports canonical carriers, obligations, blockers, status rows, and a fail-closed receipt."

stateString : String
stateString =
  "S: Boundary is checked only; the analytic preimage measure inequality and every child theorem consumption flag remain false."

latticeString : String
latticeString =
  "L: great-circle strip -> Phi preimage -> null-domain restriction -> Whitney/Fubini packet disintegration -> strip-width/Jacobian budget -> A4 output support consumer."

proposalString : String
proposalString =
  "P: Promote only after proving the Phi Jacobian lower bound, antipodal tube null mass, Sard critical null routing, Whitney/Fubini summation, and the final eta-strip preimage inequality."

governanceString : String
governanceString =
  "G: Recording flags are true; theorem, A4, leakage, Clay, and terminal promotion flags are false by refl."

gapString : String
gapString =
  "F: Missing analytic strip-preimage inequality, quantitative Jacobian lower bound, antipodal null mass, Sard null set, Fubini disintegration, bounded-overlap summation, and exceptional routing proofs."

------------------------------------------------------------------------
-- Canonical receipt.

record NSOutputStripPreimageMeasureEstimateBoundary : Set where
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
      ImportedOutputStripPreimageMeasureSupport
    outputGreatCircleStripTest :
      OutputGreatCircleStripTestCarrier
    phiNormalizeSumPreimage :
      PhiNormalizeSumPreimageCarrier
    preimageMeasureDomain :
      PreimageMeasureDomainCarrier
    stripWidthJacobianBudget :
      StripWidthJacobianBudgetCarrier
    whitneyPacketDisintegratedPreimage :
      WhitneyPacketDisintegratedPreimageCarrier
    nullExceptionalBudget :
      NullExceptionalBudgetCarrier
    estimateCarrier :
      OutputStripPreimageMeasureEstimateCarrier
    A4Consumer :
      A4OutputStripPreimageEstimateConsumer
    target :
      OutputStripPreimageMeasureEstimateTarget
    obligations :
      List OutputStripPreimageMeasureObligation
    obligationsCountIs12 :
      outputStripPreimageMeasureObligationCount ≡ 12
    blockers :
      List OutputStripPreimageMeasureBlocker
    blockerCountIs10 :
      outputStripPreimageMeasureBlockerCount ≡ 10
    statusRows :
      List OutputStripPreimageMeasureStatusRow
    statusRowCountIs10 :
      outputStripPreimageMeasureStatusRowCount ≡ 10
    boundaryRecordedTrue :
      NSOutputStripPreimageMeasureEstimateBoundaryRecorded ≡ true
    PhiNormalizeSumMapRecordedTrue :
      PhiNormalizeSumMapRecorded ≡ true
    outputGreatCircleStripTestRecordedTrue :
      outputGreatCircleStripTestRecorded ≡ true
    PhiPreimageMeasureDomainRecordedTrue :
      PhiPreimageMeasureDomainRecorded ≡ true
    stripWidthJacobianBudgetRecordedTrue :
      stripWidthJacobianBudgetRecorded ≡ true
    WhitneyFubiniPreimageDisintegrationRecordedTrue :
      WhitneyFubiniPreimageDisintegrationRecorded ≡ true
    nullExceptionalBudgetRecordedTrue :
      nullExceptionalBudgetRecorded ≡ true
    estimateCarrierRecordedTrue :
      outputStripPreimageEstimateCarrierRecorded ≡ true
    analyticPreimageMeasureEstimateStillFalse :
      analyticPreimageMeasureEstimateProved ≡ false
    PhiJacobianConsumptionStillFalse :
      PhiJacobianLowerBoundConsumedAsTheorem ≡ false
    WhitneyFubiniConsumptionStillFalse :
      WhitneyFubiniDisintegrationConsumedAsTheorem ≡ false
    antipodalConsumptionStillFalse :
      antipodalTubeNullMassConsumedAsTheorem ≡ false
    SardConsumptionStillFalse :
      SardRegularValueSlicingConsumedAsTheorem ≡ false
    outputStripConsumptionStillFalse :
      OutputGreatCircleStripSlicingConsumedAsTheorem ≡ false
    estimateTheoremStillFalse :
      OutputStripPreimageMeasureEstimateProved ≡ false
    A4WhitneyCouplingStillFalse :
      A4WhitneyCouplingInequalityProved ≡ false
    A4FourierOutputCouplingStillFalse :
      A4LeiRenTianFourierOutputCouplingProved ≡ false
    leakageIdentityStillFalse :
      triadicCompensatedLeakageIdentityProved ≡ false
    claySolvedStillFalse :
      fullClayNSSolved ≡ false
    clayPromotionStillFalse :
      clayNavierStokesPromoted ≡ false
    terminalPromotionStillFalse :
      terminalPromotion ≡ false

canonicalNSOutputStripPreimageMeasureEstimateBoundary :
  NSOutputStripPreimageMeasureEstimateBoundary
canonicalNSOutputStripPreimageMeasureEstimateBoundary =
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
        canonicalImportedOutputStripPreimageMeasureSupport
    ; outputGreatCircleStripTest =
        canonicalOutputGreatCircleStripTestCarrier
    ; phiNormalizeSumPreimage =
        canonicalPhiNormalizeSumPreimageCarrier
    ; preimageMeasureDomain =
        canonicalPreimageMeasureDomainCarrier
    ; stripWidthJacobianBudget =
        canonicalStripWidthJacobianBudgetCarrier
    ; whitneyPacketDisintegratedPreimage =
        canonicalWhitneyPacketDisintegratedPreimageCarrier
    ; nullExceptionalBudget =
        canonicalNullExceptionalBudgetCarrier
    ; estimateCarrier =
        canonicalOutputStripPreimageMeasureEstimateCarrier
    ; A4Consumer =
        canonicalA4OutputStripPreimageEstimateConsumer
    ; target =
        canonicalOutputStripPreimageMeasureEstimateTarget
    ; obligations =
        canonicalOutputStripPreimageMeasureObligations
    ; obligationsCountIs12 =
        refl
    ; blockers =
        canonicalOutputStripPreimageMeasureBlockers
    ; blockerCountIs10 =
        refl
    ; statusRows =
        canonicalOutputStripPreimageMeasureStatusRows
    ; statusRowCountIs10 =
        refl
    ; boundaryRecordedTrue =
        refl
    ; PhiNormalizeSumMapRecordedTrue =
        refl
    ; outputGreatCircleStripTestRecordedTrue =
        refl
    ; PhiPreimageMeasureDomainRecordedTrue =
        refl
    ; stripWidthJacobianBudgetRecordedTrue =
        refl
    ; WhitneyFubiniPreimageDisintegrationRecordedTrue =
        refl
    ; nullExceptionalBudgetRecordedTrue =
        refl
    ; estimateCarrierRecordedTrue =
        refl
    ; analyticPreimageMeasureEstimateStillFalse =
        refl
    ; PhiJacobianConsumptionStillFalse =
        refl
    ; WhitneyFubiniConsumptionStillFalse =
        refl
    ; antipodalConsumptionStillFalse =
        refl
    ; SardConsumptionStillFalse =
        refl
    ; outputStripConsumptionStillFalse =
        refl
    ; estimateTheoremStillFalse =
        refl
    ; A4WhitneyCouplingStillFalse =
        refl
    ; A4FourierOutputCouplingStillFalse =
        refl
    ; leakageIdentityStillFalse =
        refl
    ; claySolvedStillFalse =
        refl
    ; clayPromotionStillFalse =
        refl
    ; terminalPromotionStillFalse =
        refl
    }
