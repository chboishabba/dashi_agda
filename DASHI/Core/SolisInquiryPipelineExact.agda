module DASHI.Core.SolisInquiryPipelineExact where

------------------------------------------------------------------------
-- SOLIS SIGNAL -> RELATIONAL INQUIRY PIPELINE
--
-- The Solis/@solishood archive language treats distress/incoherence as signal
-- worth preserving rather than noise to discard.  The safe formal reading is
-- not `signal -> external system is wrong -> act`.
--
-- Existing owners reused:
--   * SolisSituatedIntegrityBridgeExact supplies the bounded synthetic SCN
--     control signal.
--   * ContradictionPreservingReasoningPipelineExact owns the separation
--     observation -> tension -> classification -> authorization -> action.
--   * RelationalEpistemicProcessSourceBridgeExact owns the generic process
--     order contextualise -> relate -> reflect -> act.
--
-- This file assembles those ideas into an inquiry discipline:
--
--   signal
--   -> preserve for inquiry
--   -> contextualise
--   -> compare declared/realised relation
--   -> reflect
--   -> only then authorize an action.
--
-- The richer trusted-friend observer in draft PR #618 is a natural later
-- provider of contextualisation evidence, but is deliberately not copied or
-- imported across draft ancestry here.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Core.DeclaredRealizedIntegrityResidualExact as Integrity
import DASHI.Core.SolisSituatedIntegrityBridgeExact as Solis
import DASHI.Core.ContradictionPreservingReasoningPipelineExact as Reasoning
import DASHI.Core.RelationalEpistemicProcessSourceBridgeExact as Relational

------------------------------------------------------------------------
-- Inquiry state and evidence roles.
------------------------------------------------------------------------

data InquiryDisposition : Set where
  preserveForInquiry discardAsNoise : InquiryDisposition

preserveSCNSignal : Solis.SCNAction → InquiryDisposition
preserveSCNSignal Solis.continueAction = preserveForInquiry
preserveSCNSignal Solis.bifurcateAction = preserveForInquiry
preserveSCNSignal Solis.quarantineAction = preserveForInquiry

data ContextReading : Set where
  lowDemandContext highDemandContext : ContextReading

data RelationReading : Set where
  declarationAligned declarationMismatch : RelationReading

data ReflectionReading : Set where
  noRepairNeeded investigateEcology : ReflectionReading

data InquiryAction : Set where
  continueSituatedly seekContextualRepair : InquiryAction

contextualiseEnvironment : Integrity.PublicEnvironment → ContextReading
contextualiseEnvironment Integrity.lowDemandThirdPlace = lowDemandContext
contextualiseEnvironment Integrity.highDemandRestrictedSpace = highDemandContext

relateDeclarationToRealization :
  Integrity.PublicEnvironment → ContextReading → RelationReading
relateDeclarationToRealization Integrity.lowDemandThirdPlace context =
  declarationAligned
relateDeclarationToRealization Integrity.highDemandRestrictedSpace context =
  declarationMismatch

reflectOnRelation :
  Integrity.PublicEnvironment →
  ContextReading →
  RelationReading →
  ReflectionReading
reflectOnRelation environment context declarationAligned = noRepairNeeded
reflectOnRelation environment context declarationMismatch = investigateEcology

actionAfterReflection :
  Integrity.PublicEnvironment →
  ContextReading →
  RelationReading →
  ReflectionReading →
  InquiryAction
actionAfterReflection environment context relation noRepairNeeded =
  continueSituatedly
actionAfterReflection environment context relation investigateEcology =
  seekContextualRepair

situatedInquiryProcess :
  Relational.RelationalEpistemicProcess
    Integrity.PublicEnvironment
    ContextReading
    RelationReading
    ReflectionReading
    InquiryAction
situatedInquiryProcess = record
  { contextualise = contextualiseEnvironment
  ; relate = relateDeclarationToRealization
  ; reflect = reflectOnRelation
  ; act = actionAfterReflection
  }

------------------------------------------------------------------------
-- Exact witnesses: same nominal declaration, different context/relation/action.
------------------------------------------------------------------------

thirdPlaceInquiryAction :
  Relational.act situatedInquiryProcess
    Integrity.lowDemandThirdPlace
    (Relational.contextualise situatedInquiryProcess Integrity.lowDemandThirdPlace)
    (Relational.relate situatedInquiryProcess
      Integrity.lowDemandThirdPlace
      (Relational.contextualise situatedInquiryProcess Integrity.lowDemandThirdPlace))
    (Relational.reflect situatedInquiryProcess
      Integrity.lowDemandThirdPlace
      (Relational.contextualise situatedInquiryProcess Integrity.lowDemandThirdPlace)
      (Relational.relate situatedInquiryProcess
        Integrity.lowDemandThirdPlace
        (Relational.contextualise situatedInquiryProcess Integrity.lowDemandThirdPlace)))
  ≡ continueSituatedly
thirdPlaceInquiryAction = refl

restrictedSpaceInquiryAction :
  Relational.act situatedInquiryProcess
    Integrity.highDemandRestrictedSpace
    (Relational.contextualise situatedInquiryProcess Integrity.highDemandRestrictedSpace)
    (Relational.relate situatedInquiryProcess
      Integrity.highDemandRestrictedSpace
      (Relational.contextualise situatedInquiryProcess Integrity.highDemandRestrictedSpace))
    (Relational.reflect situatedInquiryProcess
      Integrity.highDemandRestrictedSpace
      (Relational.contextualise situatedInquiryProcess Integrity.highDemandRestrictedSpace)
      (Relational.relate situatedInquiryProcess
        Integrity.highDemandRestrictedSpace
        (Relational.contextualise situatedInquiryProcess Integrity.highDemandRestrictedSpace)))
  ≡ seekContextualRepair
restrictedSpaceInquiryAction = refl

inquiryActionsDiffer :
  continueSituatedly ≡ seekContextualRepair → ⊥
inquiryActionsDiffer ()

------------------------------------------------------------------------
-- SCN signal is not itself the final action/authorization layer.
------------------------------------------------------------------------

data SCNSignalIsFinalAuthorizationPermission : Set where

scnSignalCannotAutoBecomeFinalAuthorization :
  SCNSignalIsFinalAuthorizationPermission → ⊥
scnSignalCannotAutoBecomeFinalAuthorization ()

reasoningTensionStillNotAuthorization :
  Reasoning.tensionPhase ≡ Reasoning.authorizationPhase → ⊥
reasoningTensionStillNotAuthorization = Reasoning.tension≠authorization

relationalContextStillNotAction :
  Relational.contextualisePhase ≡ Relational.actPhase → ⊥
relationalContextStillNotAction = Relational.contextualise≠act

------------------------------------------------------------------------
-- Claim boundary.
------------------------------------------------------------------------

record SolisInquiryBoundary : Set where
  constructor solis-inquiry-boundary
  field
    scnSignalPreservedForInquiry : Bool
    scnSignalPreservedForInquiryIsTrue : scnSignalPreservedForInquiry ≡ true
    scnSignalDirectlyProvesExternalFailure : Bool
    scnSignalDirectlyProvesExternalFailureIsFalse :
      scnSignalDirectlyProvesExternalFailure ≡ false
    scnSignalDirectlyAuthorizesAction : Bool
    scnSignalDirectlyAuthorizesActionIsFalse :
      scnSignalDirectlyAuthorizesAction ≡ false
    contextualisationRequiredBeforeSituatedAction : Bool
    contextualisationRequiredBeforeSituatedActionIsTrue :
      contextualisationRequiredBeforeSituatedAction ≡ true
    trustedFriendMayLaterSupplyContextualEvidence : Bool
    trustedFriendMayLaterSupplyContextualEvidenceIsTrue :
      trustedFriendMayLaterSupplyContextualEvidence ≡ true
    trustedFriendIsDecisionAuthority : Bool
    trustedFriendIsDecisionAuthorityIsFalse :
      trustedFriendIsDecisionAuthority ≡ false

canonicalSolisInquiryBoundary : SolisInquiryBoundary
canonicalSolisInquiryBoundary =
  solis-inquiry-boundary
    true refl
    false refl
    false refl
    true refl
    true refl
    false refl
