module DASHI.Physics.Closure.NSOutputGreatCircleStripSlicingBoundary where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; []; _∷_)

import DASHI.Physics.Closure.NSLeiRenTianOutputSupportTransferBoundary
  as OutputSupport
import DASHI.Physics.Closure.NSPhiJacobianLowerBoundBoundary
  as PhiJacobian
import DASHI.Physics.Closure.NSSardRegularValueSlicingBoundary
  as Sard
import DASHI.Physics.Closure.NSWhitneyCouplingInequalityBoundary
  as Whitney
import DASHI.Physics.Closure.NSWhitneyFubiniDisintegrationBoundary
  as Fubini

------------------------------------------------------------------------
-- NS A4 output great-circle strip slicing boundary.
--
-- Child target of NSSardRegularValueSlicingBoundary:
--
--   regular output strip around a great circle
--     -> preimage slice under Phi(theta1,theta2)
--     -> Whitney cap slicing on localized angular packets
--     -> lower-bound transfer to Fourier output support
--     -> exceptional set routing.
--
-- The intended analytic theorem is a uniform strip slicing estimate for
-- c-hat = normalize(theta1 + theta2), away from the antipodal and rank-drop
-- exceptional sets.  This module records the proof contract only.  It does
-- not construct a strip atlas, does not estimate preimage measures, does
-- not prove uniform constants, does not discharge the no-collapse consumer,
-- does not complete A4, and does not promote Navier-Stokes Clay.

listLength : {A : Set} → List A → Nat
listLength [] =
  zero
listLength (_ ∷ xs) =
  suc (listLength xs)

------------------------------------------------------------------------
-- Imported support anchors.

record ImportedOutputGreatCircleStripSlicingSupport : Set where
  field
    sardSlicingTarget :
      Sard.SardRegularValueSlicingTarget
    sardSlicingTargetIsCanonical :
      sardSlicingTarget ≡ Sard.canonicalSardRegularValueSlicingTarget
    outputGreatCircleStrip :
      Sard.OutputGreatCircleStripCarrier
    outputGreatCircleStripIsCanonical :
      outputGreatCircleStrip ≡ Sard.canonicalOutputGreatCircleStripCarrier
    whitneyPacketSlice :
      Sard.WhitneyPacketSliceCarrier
    whitneyPacketSliceIsCanonical :
      whitneyPacketSlice ≡ Sard.canonicalWhitneyPacketSliceCarrier
    stripSlicingEstimate :
      Sard.StripSlicingEstimateCarrier
    stripSlicingEstimateIsCanonical :
      stripSlicingEstimate ≡ Sard.canonicalStripSlicingEstimateCarrier
    phiJacobianLowerBound :
      PhiJacobian.PhiJacobianLowerBoundCarrier
    phiJacobianLowerBoundIsCanonical :
      phiJacobianLowerBound ≡ PhiJacobian.canonicalPhiJacobianLowerBoundCarrier
    outputStripWidthRelation :
      PhiJacobian.OutputStripWidthRelationCarrier
    outputStripWidthRelationIsCanonical :
      outputStripWidthRelation
        ≡ PhiJacobian.canonicalOutputStripWidthRelationCarrier
    whitneyOverlapLowerBound :
      Whitney.WhitneyOverlapLowerBoundCarrier
    whitneyOverlapLowerBoundIsCanonical :
      whitneyOverlapLowerBound ≡ Whitney.canonicalWhitneyOverlapLowerBoundCarrier
    fubiniExceptionalRouting :
      Fubini.ExceptionalNullSetRoutingCarrier
    fubiniExceptionalRoutingIsCanonical :
      fubiniExceptionalRouting ≡ Fubini.canonicalExceptionalNullSetRoutingCarrier
    noAngularCollapseAssumption :
      OutputSupport.NoAngularCollapseAssumption
    noAngularCollapseAssumptionIsCanonical :
      noAngularCollapseAssumption
        ≡ OutputSupport.canonicalNoAngularCollapseAssumption
    parentStripEstimateStillFalse :
      Sard.stripSlicingEstimateProved ≡ false
    parentSardSlicingStillFalse :
      Sard.SardRegularValueSlicingProved ≡ false
    parentWhitneyCouplingStillFalse :
      Whitney.A4WhitneyCouplingInequalityProved ≡ false
    parentOutputSupportStillFalse :
      OutputSupport.leiRenTianOutputSupportTransferProved ≡ false

canonicalImportedOutputGreatCircleStripSlicingSupport :
  ImportedOutputGreatCircleStripSlicingSupport
canonicalImportedOutputGreatCircleStripSlicingSupport =
  record
    { sardSlicingTarget =
        Sard.canonicalSardRegularValueSlicingTarget
    ; sardSlicingTargetIsCanonical =
        refl
    ; outputGreatCircleStrip =
        Sard.canonicalOutputGreatCircleStripCarrier
    ; outputGreatCircleStripIsCanonical =
        refl
    ; whitneyPacketSlice =
        Sard.canonicalWhitneyPacketSliceCarrier
    ; whitneyPacketSliceIsCanonical =
        refl
    ; stripSlicingEstimate =
        Sard.canonicalStripSlicingEstimateCarrier
    ; stripSlicingEstimateIsCanonical =
        refl
    ; phiJacobianLowerBound =
        PhiJacobian.canonicalPhiJacobianLowerBoundCarrier
    ; phiJacobianLowerBoundIsCanonical =
        refl
    ; outputStripWidthRelation =
        PhiJacobian.canonicalOutputStripWidthRelationCarrier
    ; outputStripWidthRelationIsCanonical =
        refl
    ; whitneyOverlapLowerBound =
        Whitney.canonicalWhitneyOverlapLowerBoundCarrier
    ; whitneyOverlapLowerBoundIsCanonical =
        refl
    ; fubiniExceptionalRouting =
        Fubini.canonicalExceptionalNullSetRoutingCarrier
    ; fubiniExceptionalRoutingIsCanonical =
        refl
    ; noAngularCollapseAssumption =
        OutputSupport.canonicalNoAngularCollapseAssumption
    ; noAngularCollapseAssumptionIsCanonical =
        refl
    ; parentStripEstimateStillFalse =
        refl
    ; parentSardSlicingStillFalse =
        refl
    ; parentWhitneyCouplingStillFalse =
        refl
    ; parentOutputSupportStillFalse =
        refl
    }

------------------------------------------------------------------------
-- Great-circle strip slicing carriers.

data GreatCircleCarrier : Set where
  greatCircleAsNormalOrthogonalOutputSet :
    OutputSupport.FourierTriadicOutputDirectionRichness →
    GreatCircleCarrier

data OutputStripWidthCarrier : Set where
  symmetricEtaStripAroundGreatCircle :
    Nat →
    GreatCircleCarrier →
    Sard.OutputGreatCircleStripCarrier →
    OutputStripWidthCarrier

data PhiPreimageStripSliceCarrier : Set where
  cHatPreimageOfOutputStripAwayFromExceptionalSets :
    OutputStripWidthCarrier →
    Sard.RegularValueCarrier →
    PhiJacobian.PhiJacobianLowerBoundCarrier →
    PhiPreimageStripSliceCarrier

data WhitneyCapStripSlicingCarrier : Set where
  intersectPhiPreimageStripWithWhitneyPacketSlices :
    PhiPreimageStripSliceCarrier →
    Sard.WhitneyPacketSliceCarrier →
    Whitney.LocalizedFramePacketLiftCarrier →
    WhitneyCapStripSlicingCarrier

data StripPreimageMeasureEstimateCarrier : Set where
  preimageSliceMeasureControlledByStripWidthAndJacobian :
    PhiPreimageStripSliceCarrier →
    PhiJacobian.OutputStripWidthRelationCarrier →
    WhitneyCapStripSlicingCarrier →
    StripPreimageMeasureEstimateCarrier

data WhitneyLowerBoundTransferCarrier : Set where
  positiveWhitneyOverlapTransfersThroughStripSlice :
    StripPreimageMeasureEstimateCarrier →
    Whitney.WhitneyOverlapLowerBoundCarrier →
    OutputSupport.FourierTriadicOutputDirectionRichness →
    WhitneyLowerBoundTransferCarrier

data StripExceptionalSetRoutingCarrier : Set where
  antipodalCriticalBoundaryAndLowVorticityStripsRoutedToNullBudget :
    Fubini.ExceptionalNullSetRoutingCarrier →
    PhiJacobian.DegenerateTriadBudgetAbsorptionCarrier →
    Whitney.SardFubiniGap →
    StripExceptionalSetRoutingCarrier

data NoCollapseConsumerCarrier : Set where
  stripLowerBoundPreventsOutputGreatCircleAvoidance :
    WhitneyLowerBoundTransferCarrier →
    StripExceptionalSetRoutingCarrier →
    OutputSupport.NoAngularCollapseAssumption →
    Whitney.NoAngularCollapseFromWhitneyCarrier →
    NoCollapseConsumerCarrier

data OutputGreatCircleStripSlicingTarget : Set where
  greatCircleStripsSliceThroughPhiWhitneyPacketsWithLowerBound :
    GreatCircleCarrier →
    OutputStripWidthCarrier →
    PhiPreimageStripSliceCarrier →
    WhitneyCapStripSlicingCarrier →
    StripPreimageMeasureEstimateCarrier →
    WhitneyLowerBoundTransferCarrier →
    StripExceptionalSetRoutingCarrier →
    NoCollapseConsumerCarrier →
    Sard.StripSlicingEstimateCarrier →
    OutputGreatCircleStripSlicingTarget

canonicalGreatCircleCarrier :
  GreatCircleCarrier
canonicalGreatCircleCarrier =
  greatCircleAsNormalOrthogonalOutputSet
    OutputSupport.canonicalFourierTriadicOutputDirectionRichness

canonicalOutputStripWidthCarrier :
  OutputStripWidthCarrier
canonicalOutputStripWidthCarrier =
  symmetricEtaStripAroundGreatCircle
    (suc zero)
    canonicalGreatCircleCarrier
    Sard.canonicalOutputGreatCircleStripCarrier

canonicalPhiPreimageStripSliceCarrier :
  PhiPreimageStripSliceCarrier
canonicalPhiPreimageStripSliceCarrier =
  cHatPreimageOfOutputStripAwayFromExceptionalSets
    canonicalOutputStripWidthCarrier
    Sard.canonicalRegularValueCarrier
    PhiJacobian.canonicalPhiJacobianLowerBoundCarrier

canonicalWhitneyCapStripSlicingCarrier :
  WhitneyCapStripSlicingCarrier
canonicalWhitneyCapStripSlicingCarrier =
  intersectPhiPreimageStripWithWhitneyPacketSlices
    canonicalPhiPreimageStripSliceCarrier
    Sard.canonicalWhitneyPacketSliceCarrier
    Whitney.canonicalLocalizedFramePacketLiftCarrier

canonicalStripPreimageMeasureEstimateCarrier :
  StripPreimageMeasureEstimateCarrier
canonicalStripPreimageMeasureEstimateCarrier =
  preimageSliceMeasureControlledByStripWidthAndJacobian
    canonicalPhiPreimageStripSliceCarrier
    PhiJacobian.canonicalOutputStripWidthRelationCarrier
    canonicalWhitneyCapStripSlicingCarrier

canonicalWhitneyLowerBoundTransferCarrier :
  WhitneyLowerBoundTransferCarrier
canonicalWhitneyLowerBoundTransferCarrier =
  positiveWhitneyOverlapTransfersThroughStripSlice
    canonicalStripPreimageMeasureEstimateCarrier
    Whitney.canonicalWhitneyOverlapLowerBoundCarrier
    OutputSupport.canonicalFourierTriadicOutputDirectionRichness

canonicalStripExceptionalSetRoutingCarrier :
  StripExceptionalSetRoutingCarrier
canonicalStripExceptionalSetRoutingCarrier =
  antipodalCriticalBoundaryAndLowVorticityStripsRoutedToNullBudget
    Fubini.canonicalExceptionalNullSetRoutingCarrier
    PhiJacobian.canonicalDegenerateTriadBudgetAbsorptionCarrier
    Whitney.proveSardRegularValueSlicingForCHatMap

canonicalNoCollapseConsumerCarrier :
  NoCollapseConsumerCarrier
canonicalNoCollapseConsumerCarrier =
  stripLowerBoundPreventsOutputGreatCircleAvoidance
    canonicalWhitneyLowerBoundTransferCarrier
    canonicalStripExceptionalSetRoutingCarrier
    OutputSupport.canonicalNoAngularCollapseAssumption
    Whitney.canonicalNoAngularCollapseFromWhitneyCarrier

canonicalOutputGreatCircleStripSlicingTarget :
  OutputGreatCircleStripSlicingTarget
canonicalOutputGreatCircleStripSlicingTarget =
  greatCircleStripsSliceThroughPhiWhitneyPacketsWithLowerBound
    canonicalGreatCircleCarrier
    canonicalOutputStripWidthCarrier
    canonicalPhiPreimageStripSliceCarrier
    canonicalWhitneyCapStripSlicingCarrier
    canonicalStripPreimageMeasureEstimateCarrier
    canonicalWhitneyLowerBoundTransferCarrier
    canonicalStripExceptionalSetRoutingCarrier
    canonicalNoCollapseConsumerCarrier
    Sard.canonicalStripSlicingEstimateCarrier

------------------------------------------------------------------------
-- Exact proof obligations and blockers.

data OutputGreatCircleStripSlicingObligation : Set where
  constructOutputGreatCircleStripAtlas :
    OutputGreatCircleStripSlicingObligation
  chooseUniformOutputStripWidthParameter :
    OutputGreatCircleStripSlicingObligation
  pullBackStripUnderPhiNormalizeSum :
    OutputGreatCircleStripSlicingObligation
  provePreimageMeasureEstimateAwayFromAntipodalAndRankDropSets :
    OutputGreatCircleStripSlicingObligation
  sliceWhitneyCapsByPulledBackOutputStrip :
    OutputGreatCircleStripSlicingObligation
  proveUniformConstantsAcrossBoundedOverlapWhitneyCover :
    OutputGreatCircleStripSlicingObligation
  routeAntipodalCriticalPacketBoundaryAndLowVorticityExceptions :
    OutputGreatCircleStripSlicingObligation
  transferPositiveWhitneyLowerBoundToOutputStripLowerBound :
    OutputGreatCircleStripSlicingObligation
  consumeNoAngularCollapseForEveryGreatCircle :
    OutputGreatCircleStripSlicingObligation
  feedEstimateIntoSardRegularValueSlicing :
    OutputGreatCircleStripSlicingObligation

canonicalOutputGreatCircleStripSlicingObligations :
  List OutputGreatCircleStripSlicingObligation
canonicalOutputGreatCircleStripSlicingObligations =
  constructOutputGreatCircleStripAtlas
  ∷ chooseUniformOutputStripWidthParameter
  ∷ pullBackStripUnderPhiNormalizeSum
  ∷ provePreimageMeasureEstimateAwayFromAntipodalAndRankDropSets
  ∷ sliceWhitneyCapsByPulledBackOutputStrip
  ∷ proveUniformConstantsAcrossBoundedOverlapWhitneyCover
  ∷ routeAntipodalCriticalPacketBoundaryAndLowVorticityExceptions
  ∷ transferPositiveWhitneyLowerBoundToOutputStripLowerBound
  ∷ consumeNoAngularCollapseForEveryGreatCircle
  ∷ feedEstimateIntoSardRegularValueSlicing
  ∷ []

outputGreatCircleStripSlicingObligationCount : Nat
outputGreatCircleStripSlicingObligationCount =
  listLength canonicalOutputGreatCircleStripSlicingObligations

outputGreatCircleStripSlicingObligationCountIs10 :
  outputGreatCircleStripSlicingObligationCount ≡ 10
outputGreatCircleStripSlicingObligationCountIs10 =
  refl

data OutputGreatCircleStripSlicingBlocker : Set where
  missingStripAtlas :
    OutputGreatCircleStripSlicingBlocker
  missingPreimageMeasureEstimate :
    OutputGreatCircleStripSlicingBlocker
  missingUniformStripConstants :
    OutputGreatCircleStripSlicingBlocker
  missingNoCollapseConsumerProof :
    OutputGreatCircleStripSlicingBlocker
  missingExceptionalSetRoutingProof :
    OutputGreatCircleStripSlicingBlocker
  missingWhitneyCapSliceSummabilityProof :
    OutputGreatCircleStripSlicingBlocker
  missingSardRegularValueFeedThrough :
    OutputGreatCircleStripSlicingBlocker
  missingA4Promotion :
    OutputGreatCircleStripSlicingBlocker
  missingClayPromotion :
    OutputGreatCircleStripSlicingBlocker

canonicalOutputGreatCircleStripSlicingBlockers :
  List OutputGreatCircleStripSlicingBlocker
canonicalOutputGreatCircleStripSlicingBlockers =
  missingStripAtlas
  ∷ missingPreimageMeasureEstimate
  ∷ missingUniformStripConstants
  ∷ missingNoCollapseConsumerProof
  ∷ missingExceptionalSetRoutingProof
  ∷ missingWhitneyCapSliceSummabilityProof
  ∷ missingSardRegularValueFeedThrough
  ∷ missingA4Promotion
  ∷ missingClayPromotion
  ∷ []

outputGreatCircleStripSlicingBlockerCount : Nat
outputGreatCircleStripSlicingBlockerCount =
  listLength canonicalOutputGreatCircleStripSlicingBlockers

outputGreatCircleStripSlicingBlockerCountIs9 :
  outputGreatCircleStripSlicingBlockerCount ≡ 9
outputGreatCircleStripSlicingBlockerCountIs9 =
  refl

data OutputGreatCircleStripSlicingStatusRow : Set where
  childBoundaryRecordedStatus :
    OutputGreatCircleStripSlicingStatusRow
  greatCircleStripCarrierRecordedStatus :
    OutputGreatCircleStripSlicingStatusRow
  outputStripWidthRecordedStatus :
    OutputGreatCircleStripSlicingStatusRow
  PhiPreimageSliceRecordedStatus :
    OutputGreatCircleStripSlicingStatusRow
  WhitneyCapSlicingRecordedStatus :
    OutputGreatCircleStripSlicingStatusRow
  lowerBoundTransferRecordedStatus :
    OutputGreatCircleStripSlicingStatusRow
  exceptionalSetRoutingRecordedStatus :
    OutputGreatCircleStripSlicingStatusRow
  noCollapseConsumerRecordedStatus :
    OutputGreatCircleStripSlicingStatusRow
  blockersRemainOpenStatus :
    OutputGreatCircleStripSlicingStatusRow
  allProofAndPromotionFlagsFalseStatus :
    OutputGreatCircleStripSlicingStatusRow

canonicalOutputGreatCircleStripSlicingStatusRows :
  List OutputGreatCircleStripSlicingStatusRow
canonicalOutputGreatCircleStripSlicingStatusRows =
  childBoundaryRecordedStatus
  ∷ greatCircleStripCarrierRecordedStatus
  ∷ outputStripWidthRecordedStatus
  ∷ PhiPreimageSliceRecordedStatus
  ∷ WhitneyCapSlicingRecordedStatus
  ∷ lowerBoundTransferRecordedStatus
  ∷ exceptionalSetRoutingRecordedStatus
  ∷ noCollapseConsumerRecordedStatus
  ∷ blockersRemainOpenStatus
  ∷ allProofAndPromotionFlagsFalseStatus
  ∷ []

outputGreatCircleStripSlicingStatusRowCount : Nat
outputGreatCircleStripSlicingStatusRowCount =
  listLength canonicalOutputGreatCircleStripSlicingStatusRows

outputGreatCircleStripSlicingStatusRowCountIs10 :
  outputGreatCircleStripSlicingStatusRowCount ≡ 10
outputGreatCircleStripSlicingStatusRowCountIs10 =
  refl

------------------------------------------------------------------------
-- Promotion-closed type.

data OutputGreatCircleStripSlicingPromotion : Set where

outputGreatCircleStripSlicingPromotionImpossibleHere :
  OutputGreatCircleStripSlicingPromotion →
  ⊥
outputGreatCircleStripSlicingPromotionImpossibleHere ()

------------------------------------------------------------------------
-- Fail-closed governance flags.

NSOutputGreatCircleStripSlicingBoundaryRecorded : Bool
NSOutputGreatCircleStripSlicingBoundaryRecorded =
  true

greatCircleStripCarrierRecorded : Bool
greatCircleStripCarrierRecorded =
  true

outputStripWidthRecorded : Bool
outputStripWidthRecorded =
  true

PhiPreimageStripSliceRecorded : Bool
PhiPreimageStripSliceRecorded =
  true

WhitneyCapStripSlicingRecorded : Bool
WhitneyCapStripSlicingRecorded =
  true

stripLowerBoundTransferRecorded : Bool
stripLowerBoundTransferRecorded =
  true

stripExceptionalSetRoutingRecorded : Bool
stripExceptionalSetRoutingRecorded =
  true

noCollapseConsumerRecorded : Bool
noCollapseConsumerRecorded =
  true

stripAtlasConstructed : Bool
stripAtlasConstructed =
  false

preimageMeasureEstimateProved : Bool
preimageMeasureEstimateProved =
  false

uniformStripConstantsProved : Bool
uniformStripConstantsProved =
  false

noCollapseConsumerProofCompleted : Bool
noCollapseConsumerProofCompleted =
  false

exceptionalSetRoutingProofCompleted : Bool
exceptionalSetRoutingProofCompleted =
  false

OutputGreatCircleStripSlicingProved : Bool
OutputGreatCircleStripSlicingProved =
  false

SardRegularValueSlicingProved : Bool
SardRegularValueSlicingProved =
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
  NSOutputGreatCircleStripSlicingBoundaryRecorded ≡ true
recordsBoundary =
  refl

recordsGreatCircleStripCarrier :
  greatCircleStripCarrierRecorded ≡ true
recordsGreatCircleStripCarrier =
  refl

recordsOutputStripWidth :
  outputStripWidthRecorded ≡ true
recordsOutputStripWidth =
  refl

recordsPhiPreimageStripSlice :
  PhiPreimageStripSliceRecorded ≡ true
recordsPhiPreimageStripSlice =
  refl

recordsWhitneyCapStripSlicing :
  WhitneyCapStripSlicingRecorded ≡ true
recordsWhitneyCapStripSlicing =
  refl

recordsStripLowerBoundTransfer :
  stripLowerBoundTransferRecorded ≡ true
recordsStripLowerBoundTransfer =
  refl

recordsStripExceptionalSetRouting :
  stripExceptionalSetRoutingRecorded ≡ true
recordsStripExceptionalSetRouting =
  refl

recordsNoCollapseConsumer :
  noCollapseConsumerRecorded ≡ true
recordsNoCollapseConsumer =
  refl

keepsStripAtlasConstructedFalse :
  stripAtlasConstructed ≡ false
keepsStripAtlasConstructedFalse =
  refl

keepsPreimageMeasureEstimateFalse :
  preimageMeasureEstimateProved ≡ false
keepsPreimageMeasureEstimateFalse =
  refl

keepsUniformStripConstantsFalse :
  uniformStripConstantsProved ≡ false
keepsUniformStripConstantsFalse =
  refl

keepsNoCollapseConsumerProofFalse :
  noCollapseConsumerProofCompleted ≡ false
keepsNoCollapseConsumerProofFalse =
  refl

keepsExceptionalSetRoutingProofFalse :
  exceptionalSetRoutingProofCompleted ≡ false
keepsExceptionalSetRoutingProofFalse =
  refl

keepsOutputGreatCircleStripSlicingFalse :
  OutputGreatCircleStripSlicingProved ≡ false
keepsOutputGreatCircleStripSlicingFalse =
  refl

keepsSardRegularValueSlicingFalse :
  SardRegularValueSlicingProved ≡ false
keepsSardRegularValueSlicingFalse =
  refl

keepsA4WhitneyCouplingInequalityFalse :
  A4WhitneyCouplingInequalityProved ≡ false
keepsA4WhitneyCouplingInequalityFalse =
  refl

keepsA4LeiRenTianFourierOutputCouplingFalse :
  A4LeiRenTianFourierOutputCouplingProved ≡ false
keepsA4LeiRenTianFourierOutputCouplingFalse =
  refl

keepsTriadicCompensatedLeakageIdentityFalse :
  triadicCompensatedLeakageIdentityProved ≡ false
keepsTriadicCompensatedLeakageIdentityFalse =
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
  "O: NS A4 strip slicing isolates the output great-circle strip estimate as a child of Sard regular-value slicing and Whitney coupling."

requirementString : String
requirementString =
  "R: Record strip carriers, Phi preimage slicing, Whitney cap slicing, lower-bound transfer, and exceptional-set routing while proving nothing."

codeArtifactString : String
codeArtifactString =
  "C: NSOutputGreatCircleStripSlicingBoundary imports Sard slicing, Phi-Jacobian, Whitney/Fubini, Whitney coupling, and output-support surfaces."

stateString : String
stateString =
  "S: Boundary is checked only; strip atlas, preimage measure estimate, uniform constants, no-collapse consumer, A4, and Clay promotion are absent."

latticeString : String
latticeString =
  "L: great-circle strip -> output width -> Phi preimage -> Whitney cap slice -> strip lower-bound transfer -> no-collapse consumer."

proposalString : String
proposalString =
  "P: Promote the parent A4 step only after strip slicing and exceptional-set routing are proved with uniform constants."

governanceString : String
governanceString =
  "G: This is fail-closed: bookkeeping flags are true, theorem and promotion flags remain false."

gapString : String
gapString =
  "F: Missing strip atlas, preimage-measure estimate, uniform strip constants, no-collapse consumer proof, and Sard/Fubini feed-through."

------------------------------------------------------------------------
-- Canonical receipt.

record NSOutputGreatCircleStripSlicingBoundary : Set where
  constructor nsOutputGreatCircleStripSlicingBoundary
  field
    importedSupport :
      ImportedOutputGreatCircleStripSlicingSupport
    greatCircle :
      GreatCircleCarrier
    outputStripWidth :
      OutputStripWidthCarrier
    phiPreimageSlice :
      PhiPreimageStripSliceCarrier
    whitneyCapSlicing :
      WhitneyCapStripSlicingCarrier
    preimageEstimate :
      StripPreimageMeasureEstimateCarrier
    lowerBoundTransfer :
      WhitneyLowerBoundTransferCarrier
    exceptionalSetRouting :
      StripExceptionalSetRoutingCarrier
    noCollapseConsumer :
      NoCollapseConsumerCarrier
    target :
      OutputGreatCircleStripSlicingTarget
    obligations :
      List OutputGreatCircleStripSlicingObligation
    blockers :
      List OutputGreatCircleStripSlicingBlocker
    statuses :
      List OutputGreatCircleStripSlicingStatusRow
    boundaryRecordedProof :
      NSOutputGreatCircleStripSlicingBoundaryRecorded ≡ true
    stripAtlasStillMissingProof :
      stripAtlasConstructed ≡ false
    preimageMeasureEstimateStillMissingProof :
      preimageMeasureEstimateProved ≡ false
    uniformStripConstantsStillMissingProof :
      uniformStripConstantsProved ≡ false
    noCollapseConsumerStillMissingProof :
      noCollapseConsumerProofCompleted ≡ false
    stripSlicingStillFalseProof :
      OutputGreatCircleStripSlicingProved ≡ false
    A4StillFalseProof :
      A4LeiRenTianFourierOutputCouplingProved ≡ false
    clayStillFalseProof :
      clayNavierStokesPromoted ≡ false
    terminalStillFalseProof :
      terminalPromotion ≡ false

canonicalNSOutputGreatCircleStripSlicingBoundary :
  NSOutputGreatCircleStripSlicingBoundary
canonicalNSOutputGreatCircleStripSlicingBoundary =
  nsOutputGreatCircleStripSlicingBoundary
    canonicalImportedOutputGreatCircleStripSlicingSupport
    canonicalGreatCircleCarrier
    canonicalOutputStripWidthCarrier
    canonicalPhiPreimageStripSliceCarrier
    canonicalWhitneyCapStripSlicingCarrier
    canonicalStripPreimageMeasureEstimateCarrier
    canonicalWhitneyLowerBoundTransferCarrier
    canonicalStripExceptionalSetRoutingCarrier
    canonicalNoCollapseConsumerCarrier
    canonicalOutputGreatCircleStripSlicingTarget
    canonicalOutputGreatCircleStripSlicingObligations
    canonicalOutputGreatCircleStripSlicingBlockers
    canonicalOutputGreatCircleStripSlicingStatusRows
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
