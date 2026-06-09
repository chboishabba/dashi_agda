module DASHI.Physics.Closure.NSBonyLipschitzAngularPushforwardBoundary where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; []; _∷_)

import DASHI.Physics.Closure.NSBonyParaproductA6RepairBoundary
  as BonyRepair
import DASHI.Physics.Closure.NSFourierOutputPushforwardBoundary
  as Pushforward
import DASHI.Physics.Closure.NSLocalizedWhitneyFramePacketEstimateBoundary
  as WhitneyPacket
import DASHI.Physics.Closure.NSWhitneyCouplingInequalityBoundary
  as WhitneyCoupling

------------------------------------------------------------------------
-- NS A4 Bony/Lipschitz angular pushforward stability boundary.
--
-- Child target of the A4 physical-to-Fourier coupling route:
--
--   Bony/paraproduct localization input
--     -> controlled perturbation of localized Whitney packet centers
--     -> off-degenerate Lipschitz stability of c-hat = normalize(a+b)
--     -> stability of the angular pushforward under Abel-window refinement
--     -> lower-order error routing into the A4 Whitney coupling budget.
--
-- This module is intentionally fail-closed.  It records the analytic proof
-- contract and exact blockers only.  It does not prove the paraproduct to
-- angular perturbation estimate, does not prove a uniform Lipschitz constant,
-- does not prove the degenerate-triad exclusion, does not prove A4, and does
-- not promote Navier-Stokes Clay.

listLength : {A : Set} → List A → Nat
listLength [] =
  zero
listLength (_ ∷ xs) =
  suc (listLength xs)

------------------------------------------------------------------------
-- Imported support anchors.

bonyParaproductRepairReference : String
bonyParaproductRepairReference =
  "DASHI.Physics.Closure.NSBonyParaproductA6RepairBoundary"

fourierOutputPushforwardReference : String
fourierOutputPushforwardReference =
  "DASHI.Physics.Closure.NSFourierOutputPushforwardBoundary"

localizedWhitneyPacketReference : String
localizedWhitneyPacketReference =
  "DASHI.Physics.Closure.NSLocalizedWhitneyFramePacketEstimateBoundary"

whitneyCouplingInequalityReference : String
whitneyCouplingInequalityReference =
  "DASHI.Physics.Closure.NSWhitneyCouplingInequalityBoundary"

bonyParaproductRepairImported : Bool
bonyParaproductRepairImported =
  true

fourierOutputPushforwardImported : Bool
fourierOutputPushforwardImported =
  true

localizedWhitneyPacketImported : Bool
localizedWhitneyPacketImported =
  true

whitneyCouplingInequalityImported : Bool
whitneyCouplingInequalityImported =
  true

record ImportedBonyLipschitzAngularPushforwardSupport : Set where
  field
    bonyRepairBoundary :
      BonyRepair.NSBonyParaproductA6RepairBoundary
    bonyRepairBoundaryIsCanonical :
      bonyRepairBoundary ≡ BonyRepair.canonicalNSBonyParaproductA6RepairBoundary
    fourierOutputPushforwardBoundary :
      Pushforward.NSFourierOutputPushforwardBoundary
    fourierOutputPushforwardBoundaryIsCanonical :
      fourierOutputPushforwardBoundary
        ≡ Pushforward.canonicalNSFourierOutputPushforwardBoundary
    localizedWhitneyPacketBoundary :
      WhitneyPacket.NSLocalizedWhitneyFramePacketEstimateBoundary
    localizedWhitneyPacketBoundaryIsCanonical :
      localizedWhitneyPacketBoundary
        ≡ WhitneyPacket.canonicalNSLocalizedWhitneyFramePacketEstimateBoundary
    whitneyCouplingBoundary :
      WhitneyCoupling.NSWhitneyCouplingInequalityBoundary
    whitneyCouplingBoundaryIsCanonical :
      whitneyCouplingBoundary
        ≡ WhitneyCoupling.canonicalNSWhitneyCouplingInequalityBoundary
    bonyRepairImportedTrue :
      bonyParaproductRepairImported ≡ true
    fourierOutputImportedTrue :
      fourierOutputPushforwardImported ≡ true
    localizedWhitneyImportedTrue :
      localizedWhitneyPacketImported ≡ true
    whitneyCouplingImportedTrue :
      whitneyCouplingInequalityImported ≡ true
    parentBonyStillDoesNotProveA6 :
      BonyRepair.A6NotProved ≡ true
    parentPushforwardStillNotProved :
      Pushforward.FourierOutputPushforwardTheoremProved ≡ false
    parentWhitneyCouplingStillNotProved :
      WhitneyCoupling.A4WhitneyCouplingInequalityProved ≡ false

canonicalImportedBonyLipschitzAngularPushforwardSupport :
  ImportedBonyLipschitzAngularPushforwardSupport
canonicalImportedBonyLipschitzAngularPushforwardSupport =
  record
    { bonyRepairBoundary =
        BonyRepair.canonicalNSBonyParaproductA6RepairBoundary
    ; bonyRepairBoundaryIsCanonical =
        refl
    ; fourierOutputPushforwardBoundary =
        Pushforward.canonicalNSFourierOutputPushforwardBoundary
    ; fourierOutputPushforwardBoundaryIsCanonical =
        refl
    ; localizedWhitneyPacketBoundary =
        WhitneyPacket.canonicalNSLocalizedWhitneyFramePacketEstimateBoundary
    ; localizedWhitneyPacketBoundaryIsCanonical =
        refl
    ; whitneyCouplingBoundary =
        WhitneyCoupling.canonicalNSWhitneyCouplingInequalityBoundary
    ; whitneyCouplingBoundaryIsCanonical =
        refl
    ; bonyRepairImportedTrue =
        refl
    ; fourierOutputImportedTrue =
        refl
    ; localizedWhitneyImportedTrue =
        refl
    ; whitneyCouplingImportedTrue =
        refl
    ; parentBonyStillDoesNotProveA6 =
        refl
    ; parentPushforwardStillNotProved =
        refl
    ; parentWhitneyCouplingStillNotProved =
        refl
    }

------------------------------------------------------------------------
-- Stability carriers.

data BonyParaproductLocalizationInput : Set where
  correctedBonyLowFrequencyLocalizationInput :
    BonyRepair.ParaproductObligation →
    BonyRepair.HighFrequencyTailObligation →
    BonyParaproductLocalizationInput

data AngularPerturbationEstimateCarrier : Set where
  paraproductPerturbationControlsAngularPacketCenter :
    BonyParaproductLocalizationInput →
    WhitneyPacket.FramePacket →
    WhitneyPacket.FrameVariationControl →
    AngularPerturbationEstimateCarrier

data OffDegenerateTriadLipschitzCarrier : Set where
  cHatNormalizeSumLipschitzAwayFromDegenerateTriads :
    Pushforward.FourierOutputPhiMap →
    Pushforward.AntipodalExclusionCarrier →
    AngularPerturbationEstimateCarrier →
    OffDegenerateTriadLipschitzCarrier

data WhitneyPacketCenterPerturbationCarrier : Set where
  perturbedWhitneyPacketCentersRemainInControlledNeighborCaps :
    WhitneyPacket.WhitneyAngularCapCover →
    WhitneyPacket.PacketOverlapControl →
    OffDegenerateTriadLipschitzCarrier →
    WhitneyPacketCenterPerturbationCarrier

data AbelWindowStabilityCarrier : Set where
  AbelWindowStableUnderBonyLipschitzAngularRefinement :
    WhitneyPacket.ScaleWindowCompatibilityControl →
    WhitneyCoupling.FourierOutputPushforwardCarrier →
    WhitneyPacketCenterPerturbationCarrier →
    AbelWindowStabilityCarrier

data LowerOrderAngularErrorRoutingCarrier : Set where
  BonyLipschitzAngularErrorsRouteIntoWhitneyCouplingBudget :
    AbelWindowStabilityCarrier →
    WhitneyCoupling.WhitneyOverlapLowerBoundCarrier →
    WhitneyCoupling.NoAngularCollapseFromWhitneyCarrier →
    LowerOrderAngularErrorRoutingCarrier

data BonyLipschitzAngularPushforwardTarget : Set where
  bonyLocalizedPerturbationsDoNotDestroyA4OutputPushforward :
    BonyParaproductLocalizationInput →
    AngularPerturbationEstimateCarrier →
    OffDegenerateTriadLipschitzCarrier →
    WhitneyPacketCenterPerturbationCarrier →
    AbelWindowStabilityCarrier →
    LowerOrderAngularErrorRoutingCarrier →
    WhitneyCoupling.WhitneyCouplingInequalityTarget →
    BonyLipschitzAngularPushforwardTarget

canonicalBonyParaproductLocalizationInput :
  BonyParaproductLocalizationInput
canonicalBonyParaproductLocalizationInput =
  correctedBonyLowFrequencyLocalizationInput
    BonyRepair.constructBonyLowHighSplit
    BonyRepair.isolateSgejStrainTail

canonicalAngularPerturbationEstimateCarrier :
  AngularPerturbationEstimateCarrier
canonicalAngularPerturbationEstimateCarrier =
  paraproductPerturbationControlsAngularPacketCenter
    canonicalBonyParaproductLocalizationInput
    WhitneyPacket.canonicalFramePacket
    WhitneyPacket.canonicalFrameVariationControl

canonicalOffDegenerateTriadLipschitzCarrier :
  OffDegenerateTriadLipschitzCarrier
canonicalOffDegenerateTriadLipschitzCarrier =
  cHatNormalizeSumLipschitzAwayFromDegenerateTriads
    Pushforward.canonicalFourierOutputPhiMap
    Pushforward.canonicalAntipodalExclusionCarrier
    canonicalAngularPerturbationEstimateCarrier

canonicalWhitneyPacketCenterPerturbationCarrier :
  WhitneyPacketCenterPerturbationCarrier
canonicalWhitneyPacketCenterPerturbationCarrier =
  perturbedWhitneyPacketCentersRemainInControlledNeighborCaps
    WhitneyPacket.canonicalWhitneyAngularCapCover
    WhitneyPacket.canonicalPacketOverlapControl
    canonicalOffDegenerateTriadLipschitzCarrier

canonicalAbelWindowStabilityCarrier :
  AbelWindowStabilityCarrier
canonicalAbelWindowStabilityCarrier =
  AbelWindowStableUnderBonyLipschitzAngularRefinement
    WhitneyPacket.canonicalScaleWindowCompatibilityControl
    WhitneyCoupling.canonicalFourierOutputPushforwardCarrier
    canonicalWhitneyPacketCenterPerturbationCarrier

canonicalLowerOrderAngularErrorRoutingCarrier :
  LowerOrderAngularErrorRoutingCarrier
canonicalLowerOrderAngularErrorRoutingCarrier =
  BonyLipschitzAngularErrorsRouteIntoWhitneyCouplingBudget
    canonicalAbelWindowStabilityCarrier
    WhitneyCoupling.canonicalWhitneyOverlapLowerBoundCarrier
    WhitneyCoupling.canonicalNoAngularCollapseFromWhitneyCarrier

canonicalBonyLipschitzAngularPushforwardTarget :
  BonyLipschitzAngularPushforwardTarget
canonicalBonyLipschitzAngularPushforwardTarget =
  bonyLocalizedPerturbationsDoNotDestroyA4OutputPushforward
    canonicalBonyParaproductLocalizationInput
    canonicalAngularPerturbationEstimateCarrier
    canonicalOffDegenerateTriadLipschitzCarrier
    canonicalWhitneyPacketCenterPerturbationCarrier
    canonicalAbelWindowStabilityCarrier
    canonicalLowerOrderAngularErrorRoutingCarrier
    WhitneyCoupling.canonicalWhitneyCouplingInequalityTarget

------------------------------------------------------------------------
-- Proof obligations and blockers.

data BonyLipschitzAngularPushforwardObligation : Set where
  importCorrectedBonyParaproductLocalization :
    BonyLipschitzAngularPushforwardObligation
  proveParaproductToAngularPerturbationEstimate :
    BonyLipschitzAngularPushforwardObligation
  proveUniformOffDegenerateCHatLipschitzConstant :
    BonyLipschitzAngularPushforwardObligation
  provePerturbedWhitneyCentersStayInNeighborCaps :
    BonyLipschitzAngularPushforwardObligation
  proveDegenerateTriadExclusionCompatibleWithWhitneyPackets :
    BonyLipschitzAngularPushforwardObligation
  proveAbelWindowStabilityUnderAngularPerturbation :
    BonyLipschitzAngularPushforwardObligation
  routeParaproductAndLipschitzErrorsAsLowerOrder :
    BonyLipschitzAngularPushforwardObligation
  feedStabilityIntoWhitneyCouplingInequality :
    BonyLipschitzAngularPushforwardObligation

canonicalBonyLipschitzAngularPushforwardObligations :
  List BonyLipschitzAngularPushforwardObligation
canonicalBonyLipschitzAngularPushforwardObligations =
  importCorrectedBonyParaproductLocalization
  ∷ proveParaproductToAngularPerturbationEstimate
  ∷ proveUniformOffDegenerateCHatLipschitzConstant
  ∷ provePerturbedWhitneyCentersStayInNeighborCaps
  ∷ proveDegenerateTriadExclusionCompatibleWithWhitneyPackets
  ∷ proveAbelWindowStabilityUnderAngularPerturbation
  ∷ routeParaproductAndLipschitzErrorsAsLowerOrder
  ∷ feedStabilityIntoWhitneyCouplingInequality
  ∷ []

bonyLipschitzAngularPushforwardObligationCount : Nat
bonyLipschitzAngularPushforwardObligationCount =
  listLength canonicalBonyLipschitzAngularPushforwardObligations

bonyLipschitzAngularPushforwardObligationCountIs8 :
  bonyLipschitzAngularPushforwardObligationCount ≡ 8
bonyLipschitzAngularPushforwardObligationCountIs8 =
  refl

data BonyLipschitzAngularErrorTerm : Set where
  paraproductAngularPerturbationError :
    BonyLipschitzAngularErrorTerm
  offDegenerateLipschitzConstantLoss :
    BonyLipschitzAngularErrorTerm
  WhitneyCenterNeighborCapLoss :
    BonyLipschitzAngularErrorTerm
  degenerateTriadTubeLoss :
    BonyLipschitzAngularErrorTerm
  AbelWindowRefinementMismatchLoss :
    BonyLipschitzAngularErrorTerm
  lowerOrderCouplingBudgetLoss :
    BonyLipschitzAngularErrorTerm

canonicalBonyLipschitzAngularErrorTerms :
  List BonyLipschitzAngularErrorTerm
canonicalBonyLipschitzAngularErrorTerms =
  paraproductAngularPerturbationError
  ∷ offDegenerateLipschitzConstantLoss
  ∷ WhitneyCenterNeighborCapLoss
  ∷ degenerateTriadTubeLoss
  ∷ AbelWindowRefinementMismatchLoss
  ∷ lowerOrderCouplingBudgetLoss
  ∷ []

bonyLipschitzAngularErrorTermCount : Nat
bonyLipschitzAngularErrorTermCount =
  listLength canonicalBonyLipschitzAngularErrorTerms

bonyLipschitzAngularErrorTermCountIs6 :
  bonyLipschitzAngularErrorTermCount ≡ 6
bonyLipschitzAngularErrorTermCountIs6 =
  refl

data BonyLipschitzAngularPushforwardBlocker : Set where
  missingParaproductToAngularPerturbationEstimate :
    BonyLipschitzAngularPushforwardBlocker
  missingLipschitzConstantUniformity :
    BonyLipschitzAngularPushforwardBlocker
  missingDegenerateTriadExclusion :
    BonyLipschitzAngularPushforwardBlocker
  missingAbelWindowStabilityProof :
    BonyLipschitzAngularPushforwardBlocker
  missingLowerOrderErrorRoutingProof :
    BonyLipschitzAngularPushforwardBlocker
  missingA4WhitneyCouplingPromotion :
    BonyLipschitzAngularPushforwardBlocker

canonicalBonyLipschitzAngularPushforwardBlockers :
  List BonyLipschitzAngularPushforwardBlocker
canonicalBonyLipschitzAngularPushforwardBlockers =
  missingParaproductToAngularPerturbationEstimate
  ∷ missingLipschitzConstantUniformity
  ∷ missingDegenerateTriadExclusion
  ∷ missingAbelWindowStabilityProof
  ∷ missingLowerOrderErrorRoutingProof
  ∷ missingA4WhitneyCouplingPromotion
  ∷ []

bonyLipschitzAngularPushforwardBlockerCount : Nat
bonyLipschitzAngularPushforwardBlockerCount =
  listLength canonicalBonyLipschitzAngularPushforwardBlockers

bonyLipschitzAngularPushforwardBlockerCountIs6 :
  bonyLipschitzAngularPushforwardBlockerCount ≡ 6
bonyLipschitzAngularPushforwardBlockerCountIs6 =
  refl

data BonyLipschitzAngularPushforwardStatusRow : Set where
  childBoundaryRecordedStatus :
    BonyLipschitzAngularPushforwardStatusRow
  bonyParaproductInputRecordedStatus :
    BonyLipschitzAngularPushforwardStatusRow
  angularPerturbationTargetRecordedStatus :
    BonyLipschitzAngularPushforwardStatusRow
  offDegenerateLipschitzTargetRecordedStatus :
    BonyLipschitzAngularPushforwardStatusRow
  WhitneyCenterPerturbationRecordedStatus :
    BonyLipschitzAngularPushforwardStatusRow
  AbelWindowStabilityTargetRecordedStatus :
    BonyLipschitzAngularPushforwardStatusRow
  lowerOrderErrorRoutingRecordedStatus :
    BonyLipschitzAngularPushforwardStatusRow
  explicitBlockersRemainStatus :
    BonyLipschitzAngularPushforwardStatusRow
  allProofAndPromotionFlagsFalseStatus :
    BonyLipschitzAngularPushforwardStatusRow

canonicalBonyLipschitzAngularPushforwardStatusRows :
  List BonyLipschitzAngularPushforwardStatusRow
canonicalBonyLipschitzAngularPushforwardStatusRows =
  childBoundaryRecordedStatus
  ∷ bonyParaproductInputRecordedStatus
  ∷ angularPerturbationTargetRecordedStatus
  ∷ offDegenerateLipschitzTargetRecordedStatus
  ∷ WhitneyCenterPerturbationRecordedStatus
  ∷ AbelWindowStabilityTargetRecordedStatus
  ∷ lowerOrderErrorRoutingRecordedStatus
  ∷ explicitBlockersRemainStatus
  ∷ allProofAndPromotionFlagsFalseStatus
  ∷ []

bonyLipschitzAngularPushforwardStatusRowCount : Nat
bonyLipschitzAngularPushforwardStatusRowCount =
  listLength canonicalBonyLipschitzAngularPushforwardStatusRows

bonyLipschitzAngularPushforwardStatusRowCountIs9 :
  bonyLipschitzAngularPushforwardStatusRowCount ≡ 9
bonyLipschitzAngularPushforwardStatusRowCountIs9 =
  refl

------------------------------------------------------------------------
-- Promotion-closed type.

data BonyLipschitzAngularPushforwardPromotion : Set where

bonyLipschitzAngularPushforwardPromotionImpossibleHere :
  BonyLipschitzAngularPushforwardPromotion →
  ⊥
bonyLipschitzAngularPushforwardPromotionImpossibleHere ()

------------------------------------------------------------------------
-- Fail-closed governance flags.

NSBonyLipschitzAngularPushforwardBoundaryRecorded : Bool
NSBonyLipschitzAngularPushforwardBoundaryRecorded =
  true

BonyParaproductLocalizationInputRecorded : Bool
BonyParaproductLocalizationInputRecorded =
  true

AngularPerturbationEstimateTargetRecorded : Bool
AngularPerturbationEstimateTargetRecorded =
  true

OffDegenerateLipschitzTargetRecorded : Bool
OffDegenerateLipschitzTargetRecorded =
  true

WhitneyPacketCenterPerturbationRecorded : Bool
WhitneyPacketCenterPerturbationRecorded =
  true

AbelWindowStabilityTargetRecorded : Bool
AbelWindowStabilityTargetRecorded =
  true

LowerOrderAngularErrorRoutingRecorded : Bool
LowerOrderAngularErrorRoutingRecorded =
  true

ParaproductToAngularPerturbationEstimateProved : Bool
ParaproductToAngularPerturbationEstimateProved =
  false

LipschitzConstantUniformityProved : Bool
LipschitzConstantUniformityProved =
  false

DegenerateTriadExclusionProved : Bool
DegenerateTriadExclusionProved =
  false

AbelWindowStabilityProofProved : Bool
AbelWindowStabilityProofProved =
  false

LowerOrderAngularErrorRoutingProved : Bool
LowerOrderAngularErrorRoutingProved =
  false

BonyLipschitzAngularPushforwardStabilityProved : Bool
BonyLipschitzAngularPushforwardStabilityProved =
  false

A4LeiRenTianFourierOutputCouplingProved : Bool
A4LeiRenTianFourierOutputCouplingProved =
  false

A6TriadicCompensatedLeakageIdentityProved : Bool
A6TriadicCompensatedLeakageIdentityProved =
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
  NSBonyLipschitzAngularPushforwardBoundaryRecorded ≡ true
recordsBoundary =
  refl

recordsBonyParaproductLocalizationInput :
  BonyParaproductLocalizationInputRecorded ≡ true
recordsBonyParaproductLocalizationInput =
  refl

recordsAngularPerturbationEstimateTarget :
  AngularPerturbationEstimateTargetRecorded ≡ true
recordsAngularPerturbationEstimateTarget =
  refl

recordsOffDegenerateLipschitzTarget :
  OffDegenerateLipschitzTargetRecorded ≡ true
recordsOffDegenerateLipschitzTarget =
  refl

recordsWhitneyPacketCenterPerturbation :
  WhitneyPacketCenterPerturbationRecorded ≡ true
recordsWhitneyPacketCenterPerturbation =
  refl

recordsAbelWindowStabilityTarget :
  AbelWindowStabilityTargetRecorded ≡ true
recordsAbelWindowStabilityTarget =
  refl

recordsLowerOrderAngularErrorRouting :
  LowerOrderAngularErrorRoutingRecorded ≡ true
recordsLowerOrderAngularErrorRouting =
  refl

keepsParaproductToAngularPerturbationEstimateFalse :
  ParaproductToAngularPerturbationEstimateProved ≡ false
keepsParaproductToAngularPerturbationEstimateFalse =
  refl

keepsLipschitzConstantUniformityFalse :
  LipschitzConstantUniformityProved ≡ false
keepsLipschitzConstantUniformityFalse =
  refl

keepsDegenerateTriadExclusionFalse :
  DegenerateTriadExclusionProved ≡ false
keepsDegenerateTriadExclusionFalse =
  refl

keepsAbelWindowStabilityProofFalse :
  AbelWindowStabilityProofProved ≡ false
keepsAbelWindowStabilityProofFalse =
  refl

keepsLowerOrderAngularErrorRoutingFalse :
  LowerOrderAngularErrorRoutingProved ≡ false
keepsLowerOrderAngularErrorRoutingFalse =
  refl

keepsBonyLipschitzAngularPushforwardStabilityFalse :
  BonyLipschitzAngularPushforwardStabilityProved ≡ false
keepsBonyLipschitzAngularPushforwardStabilityFalse =
  refl

keepsA4LeiRenTianFourierOutputCouplingFalse :
  A4LeiRenTianFourierOutputCouplingProved ≡ false
keepsA4LeiRenTianFourierOutputCouplingFalse =
  refl

keepsA6TriadicCompensatedLeakageIdentityFalse :
  A6TriadicCompensatedLeakageIdentityProved ≡ false
keepsA6TriadicCompensatedLeakageIdentityFalse =
  refl

keepsFullLocalDefectMonotonicityFalse :
  fullLocalDefectMonotonicity ≡ false
keepsFullLocalDefectMonotonicityFalse =
  refl

keepsFullClayNSSolvedFalse :
  fullClayNSSolved ≡ false
keepsFullClayNSSolvedFalse =
  refl

keepsClayNavierStokesPromotedFalse :
  clayNavierStokesPromoted ≡ false
keepsClayNavierStokesPromotedFalse =
  refl

keepsTerminalPromotionFalse :
  terminalPromotion ≡ false
keepsTerminalPromotionFalse =
  refl

------------------------------------------------------------------------
-- Canonical receipt.

orcsLpgfSummary : String
orcsLpgfSummary =
  "O NS A4 child boundary; R record Bony/Lipschitz stability of angular pushforward under paraproduct localization; C single Agda receipt importing Bony repair, Fourier output pushforward, Whitney packet, and Whitney coupling boundaries; S stability target is typed but estimates remain open; L localization input < angular perturbation < off-degenerate c-hat Lipschitz < Whitney center perturbation < Abel-window stability < A4 coupling; P prove perturbation, uniform Lipschitz, degenerate exclusion, Abel stability, and lower-order routing before A4 promotion; G all proof, Clay, and terminal promotion flags remain false; F missing paraproduct-to-angular perturbation estimate, Lipschitz constant uniformity, degenerate-triad exclusion, and Abel-window stability proof."

record NSBonyLipschitzAngularPushforwardBoundary : Set where
  field
    importedSupport :
      ImportedBonyLipschitzAngularPushforwardSupport
    bonyLocalizationInput :
      BonyParaproductLocalizationInput
    angularPerturbationEstimate :
      AngularPerturbationEstimateCarrier
    offDegenerateLipschitz :
      OffDegenerateTriadLipschitzCarrier
    WhitneyCenterPerturbation :
      WhitneyPacketCenterPerturbationCarrier
    AbelWindowStability :
      AbelWindowStabilityCarrier
    lowerOrderErrorRouting :
      LowerOrderAngularErrorRoutingCarrier
    target :
      BonyLipschitzAngularPushforwardTarget
    obligations :
      List BonyLipschitzAngularPushforwardObligation
    obligationCountProof :
      bonyLipschitzAngularPushforwardObligationCount ≡ 8
    errorTerms :
      List BonyLipschitzAngularErrorTerm
    errorTermCountProof :
      bonyLipschitzAngularErrorTermCount ≡ 6
    blockers :
      List BonyLipschitzAngularPushforwardBlocker
    blockerCountProof :
      bonyLipschitzAngularPushforwardBlockerCount ≡ 6
    statusRows :
      List BonyLipschitzAngularPushforwardStatusRow
    statusRowCountProof :
      bonyLipschitzAngularPushforwardStatusRowCount ≡ 9
    summary :
      String
    boundaryRecordedIsTrue :
      NSBonyLipschitzAngularPushforwardBoundaryRecorded ≡ true
    bonyInputRecordedIsTrue :
      BonyParaproductLocalizationInputRecorded ≡ true
    angularPerturbationRecordedIsTrue :
      AngularPerturbationEstimateTargetRecorded ≡ true
    offDegenerateLipschitzRecordedIsTrue :
      OffDegenerateLipschitzTargetRecorded ≡ true
    WhitneyPacketCenterPerturbationRecordedIsTrue :
      WhitneyPacketCenterPerturbationRecorded ≡ true
    AbelWindowStabilityRecordedIsTrue :
      AbelWindowStabilityTargetRecorded ≡ true
    lowerOrderRoutingRecordedIsTrue :
      LowerOrderAngularErrorRoutingRecorded ≡ true
    paraproductToAngularEstimateStillFalse :
      ParaproductToAngularPerturbationEstimateProved ≡ false
    LipschitzUniformityStillFalse :
      LipschitzConstantUniformityProved ≡ false
    degenerateTriadExclusionStillFalse :
      DegenerateTriadExclusionProved ≡ false
    AbelWindowStabilityStillFalse :
      AbelWindowStabilityProofProved ≡ false
    lowerOrderRoutingStillFalse :
      LowerOrderAngularErrorRoutingProved ≡ false
    stabilityTheoremStillFalse :
      BonyLipschitzAngularPushforwardStabilityProved ≡ false
    A4StillFalse :
      A4LeiRenTianFourierOutputCouplingProved ≡ false
    A6StillFalse :
      A6TriadicCompensatedLeakageIdentityProved ≡ false
    fullLocalDefectMonotonicityStillFalse :
      fullLocalDefectMonotonicity ≡ false
    fullClayNSStillFalse :
      fullClayNSSolved ≡ false
    clayNavierStokesPromotionStillFalse :
      clayNavierStokesPromoted ≡ false
    terminalPromotionStillFalse :
      terminalPromotion ≡ false

canonicalNSBonyLipschitzAngularPushforwardBoundary :
  NSBonyLipschitzAngularPushforwardBoundary
canonicalNSBonyLipschitzAngularPushforwardBoundary =
  record
    { importedSupport =
        canonicalImportedBonyLipschitzAngularPushforwardSupport
    ; bonyLocalizationInput =
        canonicalBonyParaproductLocalizationInput
    ; angularPerturbationEstimate =
        canonicalAngularPerturbationEstimateCarrier
    ; offDegenerateLipschitz =
        canonicalOffDegenerateTriadLipschitzCarrier
    ; WhitneyCenterPerturbation =
        canonicalWhitneyPacketCenterPerturbationCarrier
    ; AbelWindowStability =
        canonicalAbelWindowStabilityCarrier
    ; lowerOrderErrorRouting =
        canonicalLowerOrderAngularErrorRoutingCarrier
    ; target =
        canonicalBonyLipschitzAngularPushforwardTarget
    ; obligations =
        canonicalBonyLipschitzAngularPushforwardObligations
    ; obligationCountProof =
        refl
    ; errorTerms =
        canonicalBonyLipschitzAngularErrorTerms
    ; errorTermCountProof =
        refl
    ; blockers =
        canonicalBonyLipschitzAngularPushforwardBlockers
    ; blockerCountProof =
        refl
    ; statusRows =
        canonicalBonyLipschitzAngularPushforwardStatusRows
    ; statusRowCountProof =
        refl
    ; summary =
        orcsLpgfSummary
    ; boundaryRecordedIsTrue =
        refl
    ; bonyInputRecordedIsTrue =
        refl
    ; angularPerturbationRecordedIsTrue =
        refl
    ; offDegenerateLipschitzRecordedIsTrue =
        refl
    ; WhitneyPacketCenterPerturbationRecordedIsTrue =
        refl
    ; AbelWindowStabilityRecordedIsTrue =
        refl
    ; lowerOrderRoutingRecordedIsTrue =
        refl
    ; paraproductToAngularEstimateStillFalse =
        refl
    ; LipschitzUniformityStillFalse =
        refl
    ; degenerateTriadExclusionStillFalse =
        refl
    ; AbelWindowStabilityStillFalse =
        refl
    ; lowerOrderRoutingStillFalse =
        refl
    ; stabilityTheoremStillFalse =
        refl
    ; A4StillFalse =
        refl
    ; A6StillFalse =
        refl
    ; fullLocalDefectMonotonicityStillFalse =
        refl
    ; fullClayNSStillFalse =
        refl
    ; clayNavierStokesPromotionStillFalse =
        refl
    ; terminalPromotionStillFalse =
        refl
    }

------------------------------------------------------------------------
-- Contradictions: this receipt is not a theorem or promotion.

postulate
  bonyLipschitzBoundaryDoesNotProveParaproductAngularEstimate :
    ParaproductToAngularPerturbationEstimateProved ≡ true →
    ⊥

  bonyLipschitzBoundaryDoesNotProveUniformLipschitzConstant :
    LipschitzConstantUniformityProved ≡ true →
    ⊥

  bonyLipschitzBoundaryDoesNotProveDegenerateTriadExclusion :
    DegenerateTriadExclusionProved ≡ true →
    ⊥

  bonyLipschitzBoundaryDoesNotProveAbelWindowStability :
    AbelWindowStabilityProofProved ≡ true →
    ⊥

  bonyLipschitzBoundaryDoesNotProveA4 :
    A4LeiRenTianFourierOutputCouplingProved ≡ true →
    ⊥

  bonyLipschitzBoundaryDoesNotProveA6 :
    A6TriadicCompensatedLeakageIdentityProved ≡ true →
    ⊥

  bonyLipschitzBoundaryDoesNotPromoteClayNS :
    clayNavierStokesPromoted ≡ true →
    ⊥

  bonyLipschitzBoundaryDoesNotPromoteTerminal :
    terminalPromotion ≡ true →
    ⊥
