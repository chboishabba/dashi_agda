module DASHI.Culture.AmyEskridgeFirstPersonClaimCarrierExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- AMY ESKRIDGE MEMORIAL INVESTIGATION: FIRST-PERSON CLAIM CARRIER
--
-- A source-entitled first-person statement establishes that Amy publicly
-- reported a proposition.  It does not independently establish that the
-- underlying event occurred as described, identify an actor, or establish a
-- causal connection to her scientific work or death.
------------------------------------------------------------------------

data ClaimTopic : Set where
  residentialIntrusion : ClaimTopic
  propertyDisturbance : ClaimTopic
  surveillanceConcern : ClaimTopic
  researchSuppressionConcern : ClaimTopic
  antigravityResearchStatement : ClaimTopic

data CarrierClass : Set where
  contemporaneousRecording : CarrierClass
  archivedRecording : CarrierClass
  transcriptOfRecording : CarrierClass
  laterRetelling : CarrierClass

data CorroborationStatus : Set where
  uncorroborated : CorroborationStatus
  partiallyCorroborated : CorroborationStatus
  independentlyCorroborated : CorroborationStatus

record FirstPersonClaimCarrier : Set where
  constructor first-person-claim-carrier
  field
    speaker : String
    topic : ClaimTopic
    carrierClass : CarrierClass
    carrierLocator : String
    segmentLocator : String
    propositionSummary : String
    corroboration : CorroborationStatus

open FirstPersonClaimCarrier public

record FirstPersonClaimBoundary : Set where
  constructor first-person-claim-boundary
  field
    sourceEntitledSpeechEqualsIndependentEventProof : Bool
    firstPersonClaimIdentifiesPerpetrator : Bool
    firstPersonClaimProvesResearchLinkedTargeting : Bool
    firstPersonClaimMaySeedIndependentAcquisition : Bool
    independentCorroborationMustRemainSeparate : Bool
    memorialContextRelaxesEvidenceStandard : Bool

canonicalFirstPersonClaimBoundary : FirstPersonClaimBoundary
canonicalFirstPersonClaimBoundary =
  first-person-claim-boundary false false false true true false

------------------------------------------------------------------------
-- Publicly located carrier fixture.
--
-- This is intentionally a bounded transcription/provenance receipt.  The
-- carrier records Amy reporting repeated entries into her apartment and a cut
-- micro-USB cable.  It does not assert an independently verified intrusion.
------------------------------------------------------------------------

amyArchivedInterviewIntrusionClaim : FirstPersonClaimCarrier
amyArchivedInterviewIntrusionClaim =
  first-person-claim-carrier
    "Amy Eskridge"
    residentialIntrusion
    transcriptOfRecording
    "public archived interview/transcript located in the Amy Eskridge source lane"
    "segment describing repeated apartment entries and a cut micro-USB cable"
    "Amy publicly reported repeated entries into her apartment and described finding a micro-USB cable cut"
    uncorroborated

firstPersonClaimSeedsAcquisitionWithoutPayingCorroboration :
  FirstPersonClaimCarrier → Bool
firstPersonClaimSeedsAcquisitionWithoutPayingCorroboration _ = true
