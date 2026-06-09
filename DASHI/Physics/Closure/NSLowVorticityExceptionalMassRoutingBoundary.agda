module DASHI.Physics.Closure.NSLowVorticityExceptionalMassRoutingBoundary where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; []; _∷_)

import DASHI.Physics.Closure.NSAbelTriadicStationarityConstructionBoundary
  as Stationarity
import DASHI.Physics.Closure.NSLocalizedWhitneyFramePacketEstimateBoundary
  as Whitney
import DASHI.Physics.Closure.NSPhysicalAngularMeasureConstructionBoundary
  as Physical
import DASHI.Physics.Closure.NSWhitneyCouplingInequalityBoundary
  as Coupling

------------------------------------------------------------------------
-- NS A4 child boundary: low-vorticity/null-output exceptional mass routing.
--
-- Analytic target:
--
--   high-vorticity physical packets
--     -> discard low-vorticity exceptional set
--     -> discard null-output / undefined c-hat triads
--     -> route discarded Abel mass into lower-order residual budget
--     -> leave enough LRT support to feed the A4 Whitney coupling theorem.
--
-- This module is a proof-contract only.  It records the routing surfaces
-- and blockers needed by the Sard/Fubini A4 chain.  It does not prove the
-- high/low threshold lemma, the null-output measure bound, the Abel
-- exceptional budget, residual absorption, A4, A6, CKN/BKM, or Clay NS.

listLength : {A : Set} → List A → Nat
listLength [] =
  zero
listLength (_ ∷ xs) =
  suc (listLength xs)

------------------------------------------------------------------------
-- Imported support anchors.

physicalAngularMeasureBoundaryReference : String
physicalAngularMeasureBoundaryReference =
  "DASHI.Physics.Closure.NSPhysicalAngularMeasureConstructionBoundary"

localizedWhitneyPacketBoundaryReference : String
localizedWhitneyPacketBoundaryReference =
  "DASHI.Physics.Closure.NSLocalizedWhitneyFramePacketEstimateBoundary"

whitneyCouplingBoundaryReference : String
whitneyCouplingBoundaryReference =
  "DASHI.Physics.Closure.NSWhitneyCouplingInequalityBoundary"

abelStationarityBoundaryReference : String
abelStationarityBoundaryReference =
  "DASHI.Physics.Closure.NSAbelTriadicStationarityConstructionBoundary"

physicalAngularMeasureBoundaryImported : Bool
physicalAngularMeasureBoundaryImported =
  true

localizedWhitneyPacketBoundaryImported : Bool
localizedWhitneyPacketBoundaryImported =
  true

whitneyCouplingBoundaryImported : Bool
whitneyCouplingBoundaryImported =
  true

abelStationarityBoundaryImported : Bool
abelStationarityBoundaryImported =
  true

record ImportedLowVorticityExceptionalMassSupport : Set where
  field
    physicalBoundary :
      Physical.NSPhysicalAngularMeasureConstructionBoundary
    physicalBoundaryIsCanonical :
      physicalBoundary
        ≡ Physical.canonicalNSPhysicalAngularMeasureConstructionBoundary
    highVorticityPacketSet :
      Physical.HighVorticityPacketSetCarrier
    highVorticityPacketSetIsCanonical :
      highVorticityPacketSet
        ≡ Physical.canonicalHighVorticityPacketSet
    physicalAngularMeasure :
      Physical.PhysicalAngularMeasureCarrier
    physicalAngularMeasureIsCanonical :
      physicalAngularMeasure
        ≡ Physical.canonicalPhysicalAngularMeasure
    whitneyPacketBoundary :
      Whitney.NSLocalizedWhitneyFramePacketEstimateBoundary
    whitneyPacketBoundaryIsCanonical :
      whitneyPacketBoundary
        ≡ Whitney.canonicalNSLocalizedWhitneyFramePacketEstimateBoundary
    whitneyFramePacket :
      Whitney.FramePacket
    whitneyFramePacketIsCanonical :
      whitneyFramePacket ≡ Whitney.canonicalFramePacket
    couplingBoundary :
      Coupling.NSWhitneyCouplingInequalityBoundary
    couplingBoundaryIsCanonical :
      couplingBoundary
        ≡ Coupling.canonicalNSWhitneyCouplingInequalityBoundary
    couplingPhysicalRichness :
      Coupling.PhysicalRichnessMeasureCarrier
    couplingPhysicalRichnessIsCanonical :
      couplingPhysicalRichness
        ≡ Coupling.canonicalPhysicalRichnessMeasureCarrier
    stationarityA4Carrier :
      Stationarity.LRTOutputSupportTransferA4Carrier
    stationarityA4CarrierIsCanonical :
      stationarityA4Carrier
        ≡ Stationarity.canonicalA4LRTOutputSupportTransfer
    physicalAngularMeasureImportedTrue :
      physicalAngularMeasureBoundaryImported ≡ true
    localizedWhitneyPacketImportedTrue :
      localizedWhitneyPacketBoundaryImported ≡ true
    whitneyCouplingImportedTrue :
      whitneyCouplingBoundaryImported ≡ true
    abelStationarityImportedTrue :
      abelStationarityBoundaryImported ≡ true

canonicalImportedLowVorticityExceptionalMassSupport :
  ImportedLowVorticityExceptionalMassSupport
canonicalImportedLowVorticityExceptionalMassSupport =
  record
    { physicalBoundary =
        Physical.canonicalNSPhysicalAngularMeasureConstructionBoundary
    ; physicalBoundaryIsCanonical =
        refl
    ; highVorticityPacketSet =
        Physical.canonicalHighVorticityPacketSet
    ; highVorticityPacketSetIsCanonical =
        refl
    ; physicalAngularMeasure =
        Physical.canonicalPhysicalAngularMeasure
    ; physicalAngularMeasureIsCanonical =
        refl
    ; whitneyPacketBoundary =
        Whitney.canonicalNSLocalizedWhitneyFramePacketEstimateBoundary
    ; whitneyPacketBoundaryIsCanonical =
        refl
    ; whitneyFramePacket =
        Whitney.canonicalFramePacket
    ; whitneyFramePacketIsCanonical =
        refl
    ; couplingBoundary =
        Coupling.canonicalNSWhitneyCouplingInequalityBoundary
    ; couplingBoundaryIsCanonical =
        refl
    ; couplingPhysicalRichness =
        Coupling.canonicalPhysicalRichnessMeasureCarrier
    ; couplingPhysicalRichnessIsCanonical =
        refl
    ; stationarityA4Carrier =
        Stationarity.canonicalA4LRTOutputSupportTransfer
    ; stationarityA4CarrierIsCanonical =
        refl
    ; physicalAngularMeasureImportedTrue =
        refl
    ; localizedWhitneyPacketImportedTrue =
        refl
    ; whitneyCouplingImportedTrue =
        refl
    ; abelStationarityImportedTrue =
        refl
    }

------------------------------------------------------------------------
-- Exceptional-mass routing carriers.

data HighVorticityPacketRestrictionCarrier : Set where
  restrictA4MeasureToHighVorticityPackets :
    Physical.HighVorticityPacketSetCarrier →
    Physical.PhysicalAngularMeasureCarrier →
    Whitney.FramePacket →
    HighVorticityPacketRestrictionCarrier

data LowVorticityExceptionalSetCarrier : Set where
  lowVorticityBelowThresholdExceptionalSet :
    Physical.TypeIVorticityPacketCarrier →
    Physical.HighVorticityThresholdCarrier →
    LowVorticityExceptionalSetCarrier

data NullOutputCHatExclusionCarrier : Set where
  excludeZeroOrAntipodalNormalizeSumTriads :
    Coupling.FourierOutputPushforwardCarrier →
    Whitney.AnnularExclusionControl →
    NullOutputCHatExclusionCarrier

data AbelExceptionalMassRoutingCarrier : Set where
  routeLowAndNullOutputMassThroughAbelWindow :
    LowVorticityExceptionalSetCarrier →
    NullOutputCHatExclusionCarrier →
    Stationarity.ApproximateTNSStationarityA3Carrier →
    AbelExceptionalMassRoutingCarrier

data LowerOrderResidualBudgetCarrier : Set where
  absorbExceptionalMassIntoLowerOrderResidual :
    AbelExceptionalMassRoutingCarrier →
    Stationarity.BoundedMassA1Carrier →
    LowerOrderResidualBudgetCarrier

data LRTSupportConsumerCarrier : Set where
  consumeRemainingHighVorticitySupportForLRT :
    HighVorticityPacketRestrictionCarrier →
    LowerOrderResidualBudgetCarrier →
    Coupling.NoAngularCollapseFromWhitneyCarrier →
    Stationarity.LRTOutputSupportTransferA4Carrier →
    LRTSupportConsumerCarrier

data LowVorticityExceptionalMassRoutingTarget : Set where
  exceptionalLowAndNullOutputMassDoesNotBreakA4Support :
    HighVorticityPacketRestrictionCarrier →
    LowVorticityExceptionalSetCarrier →
    NullOutputCHatExclusionCarrier →
    AbelExceptionalMassRoutingCarrier →
    LowerOrderResidualBudgetCarrier →
    LRTSupportConsumerCarrier →
    LowVorticityExceptionalMassRoutingTarget

canonicalHighVorticityPacketRestriction :
  HighVorticityPacketRestrictionCarrier
canonicalHighVorticityPacketRestriction =
  restrictA4MeasureToHighVorticityPackets
    Physical.canonicalHighVorticityPacketSet
    Physical.canonicalPhysicalAngularMeasure
    Whitney.canonicalFramePacket

canonicalLowVorticityExceptionalSet :
  LowVorticityExceptionalSetCarrier
canonicalLowVorticityExceptionalSet =
  lowVorticityBelowThresholdExceptionalSet
    Physical.canonicalTypeIVorticityPacket
    Physical.canonicalHighVorticityThreshold

canonicalNullOutputCHatExclusion :
  NullOutputCHatExclusionCarrier
canonicalNullOutputCHatExclusion =
  excludeZeroOrAntipodalNormalizeSumTriads
    Coupling.canonicalFourierOutputPushforwardCarrier
    Whitney.canonicalAnnularExclusionControl

canonicalAbelExceptionalMassRouting :
  AbelExceptionalMassRoutingCarrier
canonicalAbelExceptionalMassRouting =
  routeLowAndNullOutputMassThroughAbelWindow
    canonicalLowVorticityExceptionalSet
    canonicalNullOutputCHatExclusion
    Stationarity.canonicalA3ApproximateTNSStationarity

canonicalLowerOrderResidualBudget :
  LowerOrderResidualBudgetCarrier
canonicalLowerOrderResidualBudget =
  absorbExceptionalMassIntoLowerOrderResidual
    canonicalAbelExceptionalMassRouting
    Stationarity.canonicalA1BoundedMass

canonicalLRTSupportConsumer :
  LRTSupportConsumerCarrier
canonicalLRTSupportConsumer =
  consumeRemainingHighVorticitySupportForLRT
    canonicalHighVorticityPacketRestriction
    canonicalLowerOrderResidualBudget
    Coupling.canonicalNoAngularCollapseFromWhitneyCarrier
    Stationarity.canonicalA4LRTOutputSupportTransfer

canonicalLowVorticityExceptionalMassRoutingTarget :
  LowVorticityExceptionalMassRoutingTarget
canonicalLowVorticityExceptionalMassRoutingTarget =
  exceptionalLowAndNullOutputMassDoesNotBreakA4Support
    canonicalHighVorticityPacketRestriction
    canonicalLowVorticityExceptionalSet
    canonicalNullOutputCHatExclusion
    canonicalAbelExceptionalMassRouting
    canonicalLowerOrderResidualBudget
    canonicalLRTSupportConsumer

------------------------------------------------------------------------
-- Obligations, blockers, and statuses.

data LowVorticityExceptionalMassRoutingObligation : Set where
  defineHighVorticityPacketRestriction :
    LowVorticityExceptionalMassRoutingObligation
  defineLowVorticityExceptionalSet :
    LowVorticityExceptionalMassRoutingObligation
  defineNullOutputCHatExclusion :
    LowVorticityExceptionalMassRoutingObligation
  proveAbelWindowExceptionalMassRouting :
    LowVorticityExceptionalMassRoutingObligation
  proveLowerOrderResidualBudgetAbsorbsExceptionalMass :
    LowVorticityExceptionalMassRoutingObligation
  proveRemainingHighVorticitySupportStillFeedsLRT :
    LowVorticityExceptionalMassRoutingObligation
  keepA4A6AndClayPromotionClosed :
    LowVorticityExceptionalMassRoutingObligation

canonicalLowVorticityExceptionalMassRoutingObligations :
  List LowVorticityExceptionalMassRoutingObligation
canonicalLowVorticityExceptionalMassRoutingObligations =
  defineHighVorticityPacketRestriction
  ∷ defineLowVorticityExceptionalSet
  ∷ defineNullOutputCHatExclusion
  ∷ proveAbelWindowExceptionalMassRouting
  ∷ proveLowerOrderResidualBudgetAbsorbsExceptionalMass
  ∷ proveRemainingHighVorticitySupportStillFeedsLRT
  ∷ keepA4A6AndClayPromotionClosed
  ∷ []

lowVorticityExceptionalMassRoutingObligationCount : Nat
lowVorticityExceptionalMassRoutingObligationCount =
  listLength canonicalLowVorticityExceptionalMassRoutingObligations

lowVorticityExceptionalMassRoutingObligationCountIs7 :
  lowVorticityExceptionalMassRoutingObligationCount ≡ 7
lowVorticityExceptionalMassRoutingObligationCountIs7 =
  refl

data LowVorticityExceptionalMassRoutingBlocker : Set where
  missingHighLowVorticityThresholdLemma :
    LowVorticityExceptionalMassRoutingBlocker
  missingNullOutputMeasureBound :
    LowVorticityExceptionalMassRoutingBlocker
  missingAbelExceptionalBudget :
    LowVorticityExceptionalMassRoutingBlocker
  missingResidualAbsorption :
    LowVorticityExceptionalMassRoutingBlocker
  missingLRTSupportAfterDiscardConsumer :
    LowVorticityExceptionalMassRoutingBlocker
  proofAndPromotionRemainClosed :
    LowVorticityExceptionalMassRoutingBlocker

canonicalLowVorticityExceptionalMassRoutingBlockers :
  List LowVorticityExceptionalMassRoutingBlocker
canonicalLowVorticityExceptionalMassRoutingBlockers =
  missingHighLowVorticityThresholdLemma
  ∷ missingNullOutputMeasureBound
  ∷ missingAbelExceptionalBudget
  ∷ missingResidualAbsorption
  ∷ missingLRTSupportAfterDiscardConsumer
  ∷ proofAndPromotionRemainClosed
  ∷ []

lowVorticityExceptionalMassRoutingBlockerCount : Nat
lowVorticityExceptionalMassRoutingBlockerCount =
  listLength canonicalLowVorticityExceptionalMassRoutingBlockers

lowVorticityExceptionalMassRoutingBlockerCountIs6 :
  lowVorticityExceptionalMassRoutingBlockerCount ≡ 6
lowVorticityExceptionalMassRoutingBlockerCountIs6 =
  refl

data LowVorticityExceptionalMassRoutingStatus : Set where
  boundaryRecordedStatus :
    LowVorticityExceptionalMassRoutingStatus
  highVorticityRestrictionRecordedStatus :
    LowVorticityExceptionalMassRoutingStatus
  lowVorticityExceptionalSetRecordedStatus :
    LowVorticityExceptionalMassRoutingStatus
  nullOutputExclusionRecordedStatus :
    LowVorticityExceptionalMassRoutingStatus
  abelMassRoutingRecordedStatus :
    LowVorticityExceptionalMassRoutingStatus
  lowerOrderResidualBudgetRecordedStatus :
    LowVorticityExceptionalMassRoutingStatus
  lrtSupportConsumerRecordedStatus :
    LowVorticityExceptionalMassRoutingStatus
  blockersRemainOpenStatus :
    LowVorticityExceptionalMassRoutingStatus
  promotionClosedStatus :
    LowVorticityExceptionalMassRoutingStatus

canonicalLowVorticityExceptionalMassRoutingStatuses :
  List LowVorticityExceptionalMassRoutingStatus
canonicalLowVorticityExceptionalMassRoutingStatuses =
  boundaryRecordedStatus
  ∷ highVorticityRestrictionRecordedStatus
  ∷ lowVorticityExceptionalSetRecordedStatus
  ∷ nullOutputExclusionRecordedStatus
  ∷ abelMassRoutingRecordedStatus
  ∷ lowerOrderResidualBudgetRecordedStatus
  ∷ lrtSupportConsumerRecordedStatus
  ∷ blockersRemainOpenStatus
  ∷ promotionClosedStatus
  ∷ []

lowVorticityExceptionalMassRoutingStatusCount : Nat
lowVorticityExceptionalMassRoutingStatusCount =
  listLength canonicalLowVorticityExceptionalMassRoutingStatuses

lowVorticityExceptionalMassRoutingStatusCountIs9 :
  lowVorticityExceptionalMassRoutingStatusCount ≡ 9
lowVorticityExceptionalMassRoutingStatusCountIs9 =
  refl

------------------------------------------------------------------------
-- Promotion-closed type.

data LowVorticityExceptionalMassRoutingPromotion : Set where

lowVorticityExceptionalMassRoutingPromotionImpossibleHere :
  LowVorticityExceptionalMassRoutingPromotion →
  ⊥
lowVorticityExceptionalMassRoutingPromotionImpossibleHere ()

------------------------------------------------------------------------
-- Fail-closed governance flags.

NSLowVorticityExceptionalMassRoutingBoundaryRecorded : Bool
NSLowVorticityExceptionalMassRoutingBoundaryRecorded =
  true

highVorticityPacketRestrictionRecorded : Bool
highVorticityPacketRestrictionRecorded =
  true

lowVorticityExceptionalSetRecorded : Bool
lowVorticityExceptionalSetRecorded =
  true

nullOutputCHatExclusionRecorded : Bool
nullOutputCHatExclusionRecorded =
  true

AbelExceptionalMassRoutingRecorded : Bool
AbelExceptionalMassRoutingRecorded =
  true

lowerOrderResidualBudgetRecorded : Bool
lowerOrderResidualBudgetRecorded =
  true

LRTSupportConsumerRecorded : Bool
LRTSupportConsumerRecorded =
  true

highLowVorticityThresholdLemmaProved : Bool
highLowVorticityThresholdLemmaProved =
  false

nullOutputMeasureBoundProved : Bool
nullOutputMeasureBoundProved =
  false

AbelExceptionalBudgetProved : Bool
AbelExceptionalBudgetProved =
  false

residualAbsorptionProved : Bool
residualAbsorptionProved =
  false

LRTSupportAfterDiscardProved : Bool
LRTSupportAfterDiscardProved =
  false

A4LowVorticityExceptionalMassRoutingProved : Bool
A4LowVorticityExceptionalMassRoutingProved =
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

keepsHighLowVorticityThresholdLemmaFalse :
  highLowVorticityThresholdLemmaProved ≡ false
keepsHighLowVorticityThresholdLemmaFalse =
  refl

keepsNullOutputMeasureBoundFalse :
  nullOutputMeasureBoundProved ≡ false
keepsNullOutputMeasureBoundFalse =
  refl

keepsAbelExceptionalBudgetFalse :
  AbelExceptionalBudgetProved ≡ false
keepsAbelExceptionalBudgetFalse =
  refl

keepsResidualAbsorptionFalse :
  residualAbsorptionProved ≡ false
keepsResidualAbsorptionFalse =
  refl

keepsLRTSupportAfterDiscardFalse :
  LRTSupportAfterDiscardProved ≡ false
keepsLRTSupportAfterDiscardFalse =
  refl

keepsA4LowVorticityRoutingFalse :
  A4LowVorticityExceptionalMassRoutingProved ≡ false
keepsA4LowVorticityRoutingFalse =
  refl

keepsA4FourierOutputCouplingFalse :
  A4LeiRenTianFourierOutputCouplingProved ≡ false
keepsA4FourierOutputCouplingFalse =
  refl

keepsA6TriadicLeakageFalse :
  A6TriadicCompensatedLeakageIdentityProved ≡ false
keepsA6TriadicLeakageFalse =
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
  "O: Worker-4 child boundary routes low-vorticity and null-output exceptional mass inside the NS A4 Whitney/Fubini coupling chain."

requirementString : String
requirementString =
  "R: Record high-vorticity packet restriction, low-vorticity exceptional set, null-output c-hat exclusion, Abel mass routing, residual budget, and LRT support consumer."

codeArtifactString : String
codeArtifactString =
  "C: NSLowVorticityExceptionalMassRoutingBoundary imports physical angular measure, localized Whitney packet, Whitney coupling, and Abel stationarity boundaries."

stateString : String
stateString =
  "S: Boundary is checked and fail-closed; threshold, null-output measure, Abel exceptional budget, and residual absorption proofs remain open."

latticeString : String
latticeString =
  "L: high-vorticity restriction -> exceptional discard -> Abel budget -> residual absorption -> remaining LRT support -> A4 output coupling."

proposalString : String
proposalString =
  "P: Promote only after proving the high/low threshold lemma, null-output bound, Abel exceptional budget, residual absorption, and LRT support preservation."

governanceString : String
governanceString =
  "G: Governance remains fail-closed: recording flags are true while theorem, A4, A6, Clay, and terminal promotion flags are false."

gapString : String
gapString =
  "F: Open gaps are missing high/low vorticity threshold lemma, null-output measure bound, Abel exceptional budget, residual absorption, and support-after-discard consumer."

------------------------------------------------------------------------
-- Canonical receipt.

record NSLowVorticityExceptionalMassRoutingBoundary : Set where
  constructor nsLowVorticityExceptionalMassRoutingBoundary
  field
    importedSupport :
      ImportedLowVorticityExceptionalMassSupport
    importedSupportIsCanonical :
      importedSupport ≡ canonicalImportedLowVorticityExceptionalMassSupport
    highVorticityPacketRestriction :
      HighVorticityPacketRestrictionCarrier
    highVorticityPacketRestrictionIsCanonical :
      highVorticityPacketRestriction ≡ canonicalHighVorticityPacketRestriction
    lowVorticityExceptionalSet :
      LowVorticityExceptionalSetCarrier
    lowVorticityExceptionalSetIsCanonical :
      lowVorticityExceptionalSet ≡ canonicalLowVorticityExceptionalSet
    nullOutputCHatExclusion :
      NullOutputCHatExclusionCarrier
    nullOutputCHatExclusionIsCanonical :
      nullOutputCHatExclusion ≡ canonicalNullOutputCHatExclusion
    abelExceptionalMassRouting :
      AbelExceptionalMassRoutingCarrier
    abelExceptionalMassRoutingIsCanonical :
      abelExceptionalMassRouting ≡ canonicalAbelExceptionalMassRouting
    lowerOrderResidualBudget :
      LowerOrderResidualBudgetCarrier
    lowerOrderResidualBudgetIsCanonical :
      lowerOrderResidualBudget ≡ canonicalLowerOrderResidualBudget
    lrtSupportConsumer :
      LRTSupportConsumerCarrier
    lrtSupportConsumerIsCanonical :
      lrtSupportConsumer ≡ canonicalLRTSupportConsumer
    target :
      LowVorticityExceptionalMassRoutingTarget
    targetIsCanonical :
      target ≡ canonicalLowVorticityExceptionalMassRoutingTarget
    obligations :
      List LowVorticityExceptionalMassRoutingObligation
    obligationsAreCanonical :
      obligations ≡ canonicalLowVorticityExceptionalMassRoutingObligations
    blockers :
      List LowVorticityExceptionalMassRoutingBlocker
    blockersAreCanonical :
      blockers ≡ canonicalLowVorticityExceptionalMassRoutingBlockers
    statuses :
      List LowVorticityExceptionalMassRoutingStatus
    statusesAreCanonical :
      statuses ≡ canonicalLowVorticityExceptionalMassRoutingStatuses
    O : String
    OIsCanonical : O ≡ organizationString
    R : String
    RIsCanonical : R ≡ requirementString
    C : String
    CIsCanonical : C ≡ codeArtifactString
    S : String
    SIsCanonical : S ≡ stateString
    L : String
    LIsCanonical : L ≡ latticeString
    P : String
    PIsCanonical : P ≡ proposalString
    G : String
    GIsCanonical : G ≡ governanceString
    F : String
    FIsCanonical : F ≡ gapString
    boundaryRecorded :
      NSLowVorticityExceptionalMassRoutingBoundaryRecorded ≡ true
    highRestrictionRecorded :
      highVorticityPacketRestrictionRecorded ≡ true
    lowExceptionalRecorded :
      lowVorticityExceptionalSetRecorded ≡ true
    nullOutputRecorded :
      nullOutputCHatExclusionRecorded ≡ true
    abelRoutingRecorded :
      AbelExceptionalMassRoutingRecorded ≡ true
    residualBudgetRecorded :
      lowerOrderResidualBudgetRecorded ≡ true
    lrtConsumerRecorded :
      LRTSupportConsumerRecorded ≡ true
    thresholdLemmaFalse :
      highLowVorticityThresholdLemmaProved ≡ false
    nullOutputBoundFalse :
      nullOutputMeasureBoundProved ≡ false
    abelBudgetFalse :
      AbelExceptionalBudgetProved ≡ false
    residualAbsorptionFalse :
      residualAbsorptionProved ≡ false
    lrtSupportAfterDiscardFalse :
      LRTSupportAfterDiscardProved ≡ false
    A4RoutingFalse :
      A4LowVorticityExceptionalMassRoutingProved ≡ false
    A4CouplingFalse :
      A4LeiRenTianFourierOutputCouplingProved ≡ false
    A6LeakageFalse :
      A6TriadicCompensatedLeakageIdentityProved ≡ false
    claySolvedFalse :
      fullClayNSSolved ≡ false
    clayPromotionFalse :
      clayNavierStokesPromoted ≡ false
    terminalPromotionFalse :
      terminalPromotion ≡ false

open NSLowVorticityExceptionalMassRoutingBoundary public

canonicalNSLowVorticityExceptionalMassRoutingBoundary :
  NSLowVorticityExceptionalMassRoutingBoundary
canonicalNSLowVorticityExceptionalMassRoutingBoundary =
  nsLowVorticityExceptionalMassRoutingBoundary
    canonicalImportedLowVorticityExceptionalMassSupport
    refl
    canonicalHighVorticityPacketRestriction
    refl
    canonicalLowVorticityExceptionalSet
    refl
    canonicalNullOutputCHatExclusion
    refl
    canonicalAbelExceptionalMassRouting
    refl
    canonicalLowerOrderResidualBudget
    refl
    canonicalLRTSupportConsumer
    refl
    canonicalLowVorticityExceptionalMassRoutingTarget
    refl
    canonicalLowVorticityExceptionalMassRoutingObligations
    refl
    canonicalLowVorticityExceptionalMassRoutingBlockers
    refl
    canonicalLowVorticityExceptionalMassRoutingStatuses
    refl
    organizationString
    refl
    requirementString
    refl
    codeArtifactString
    refl
    stateString
    refl
    latticeString
    refl
    proposalString
    refl
    governanceString
    refl
    gapString
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
