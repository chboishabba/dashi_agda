module DASHI.Education.DigitalESDParticipantGovernanceContextTransferExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Cognition.PNF.LearningAlgebra as Learning
import DASHI.Biology.StudentVoiceEpistemicAgencyBridge as Voice
import DASHI.Education.AliceBrownDigitalESDEpistemicGovernanceBridgeExact as Alice

------------------------------------------------------------------------
-- PARTICIPANT GOVERNANCE / CONTEXT-TRANSFER THIN BRIDGE
--
-- DASHI synthesis.  The canonical Alice/voice owners supply source-bounded
-- methodological constraints; LearningAlgebra supplies the canonical context
-- generalisation receipt.  None of those sources or citations manufactures
-- authority for a new participant population.
--
-- Attribution invariant:
--   * source identity + role + same-object status survive the transfer;
--   * citation imports neither proof nor authority;
--   * acquisition order does not imply payment order;
--   * downstream payment cannot skip an unpaid dependency.
------------------------------------------------------------------------

-- The target context is an index, not a free text assertion inside the
-- receipt.  An authority receipt for another context therefore cannot inhabit
-- the type required by an admission for this context.
record ParticipantAuthorityReceipt (targetContext : String) : Set where
  constructor participant-authority-receipt
  field
    participantPopulationIdentity : String
    sourceRoleReference : String
    sameObjectEvidenceReference : String
    questionShapingEvidenceReference : String
    codingFrameContestEvidenceReference : String
    coInterpretationEvidenceReference : String
    chooseOrRejectHandleEvidenceReference : String
    evidenceReturnReviewReference : String
    voluntaryParticipationEvidenceReference : String

    samePopulationAndContextObserved : Bool
    samePopulationAndContextObservedIsTrue :
      samePopulationAndContextObserved ≡ true

    constitutiveAgencyObservedLocally : Bool
    constitutiveAgencyObservedLocallyIsTrue :
      constitutiveAgencyObservedLocally ≡ true

    authorityAutomaticallyTransfersBeyondTargetContext : Bool
    authorityAutomaticallyTransfersBeyondTargetContextIsFalse :
      authorityAutomaticallyTransfersBeyondTargetContext ≡ false

open ParticipantAuthorityReceipt public

record ParticipantGovernanceContextTransferAdmission : Set where
  constructor participant-governance-context-transfer-admission
  field
    contextGeneralisationReceipt : Learning.ContextGeneralisationReceipt
    participantAuthorityReceipt :
      ParticipantAuthorityReceipt
        (Learning.targetContext contextGeneralisationReceipt)

    canonicalStudentVoiceBridge : Voice.StudentVoiceEpistemicAgencyBridge
    canonicalStudentVoiceBridgeIsCanonical :
      canonicalStudentVoiceBridge ≡ Voice.canonicalStudentVoiceEpistemicAgencyBridge

    canonicalAliceGovernanceBridge :
      Alice.AliceBrownDigitalESDEpistemicGovernanceBridge
    canonicalAliceGovernanceBridgeIsCanonical :
      canonicalAliceGovernanceBridge
      ≡ Alice.canonicalAliceBrownDigitalESDEpistemicGovernanceBridge

    sourceContextRetained : String
    sourceContextRetainedIsExact :
      sourceContextRetained
      ≡ Learning.sourceContext contextGeneralisationReceipt

    targetContextRetained : String
    targetContextRetainedIsExact :
      targetContextRetained
      ≡ Learning.targetContext contextGeneralisationReceipt

    transportCertificateRetained : String
    transportCertificateRetainedIsExact :
      transportCertificateRetained
      ≡ Learning.transportCertificate contextGeneralisationReceipt

    generalisationRemainsNonAutomatic :
      Learning.generalisationIsAutomatic contextGeneralisationReceipt ≡ false

    sourceRoleRetained : Bool
    sourceRoleRetainedIsTrue : sourceRoleRetained ≡ true

    sameObjectStatusRetained : Bool
    sameObjectStatusRetainedIsTrue : sameObjectStatusRetained ≡ true

    admissionAutomaticallyCreatesAuthority : Bool
    admissionAutomaticallyCreatesAuthorityIsFalse :
      admissionAutomaticallyCreatesAuthority ≡ false

open ParticipantGovernanceContextTransferAdmission public

admitParticipantGovernanceContextTransfer :
  (context : Learning.ContextGeneralisationReceipt) →
  ParticipantAuthorityReceipt (Learning.targetContext context) →
  ParticipantGovernanceContextTransferAdmission
admitParticipantGovernanceContextTransfer context authority =
  participant-governance-context-transfer-admission
    context
    authority
    Voice.canonicalStudentVoiceEpistemicAgencyBridge refl
    Alice.canonicalAliceBrownDigitalESDEpistemicGovernanceBridge refl
    (Learning.sourceContext context) refl
    (Learning.targetContext context) refl
    (Learning.transportCertificate context) refl
    (Learning.generalisationIsAutomaticIsFalse context)
    true refl
    true refl
    false refl

------------------------------------------------------------------------
-- Non-promotion firewalls.
------------------------------------------------------------------------

data LiteratureCreatesParticipantAuthority : Set where
literatureDoesNotCreateParticipantAuthority :
  LiteratureCreatesParticipantAuthority → ⊥
literatureDoesNotCreateParticipantAuthority ()

data ConsentCreatesParticipantAuthority : Set where
consentDoesNotCreateParticipantAuthority :
  ConsentCreatesParticipantAuthority → ⊥
consentDoesNotCreateParticipantAuthority ()

data ProceduralEthicsCreatesParticipantAuthority : Set where
proceduralEthicsDoesNotCreateParticipantAuthority :
  ProceduralEthicsCreatesParticipantAuthority → ⊥
proceduralEthicsDoesNotCreateParticipantAuthority ()

data AliceCorpusCreatesLocalParticipantAuthority : Set where
aliceCorpusDoesNotCreateLocalParticipantAuthority :
  AliceCorpusCreatesLocalParticipantAuthority → ⊥
aliceCorpusDoesNotCreateLocalParticipantAuthority ()

data ContextSimilarityCreatesGeneralisationReceipt : Set where
contextSimilarityDoesNotCreateGeneralisationReceipt :
  ContextSimilarityCreatesGeneralisationReceipt → ⊥
contextSimilarityDoesNotCreateGeneralisationReceipt ()

data PaidContextReceiptSkipsAuthorityReceipt : Set where
paidContextReceiptDoesNotSkipAuthorityReceipt :
  PaidContextReceiptSkipsAuthorityReceipt → ⊥
paidContextReceiptDoesNotSkipAuthorityReceipt ()

data PaidAuthorityReceiptSkipsContextReceipt : Set where
paidAuthorityReceiptDoesNotSkipContextReceipt :
  PaidAuthorityReceiptSkipsContextReceipt → ⊥
paidAuthorityReceiptDoesNotSkipContextReceipt ()

------------------------------------------------------------------------
-- Boundary: this bridge is a rule for admitting a transfer claim, not an
-- empirical claim that the present conceptual-review manuscript has performed
-- a local participant-authority study.
------------------------------------------------------------------------

record ParticipantGovernanceContextTransferBoundary : Set where
  constructor participant-governance-context-transfer-boundary
  field
    sourceRoleAndSameObjectRetained : Bool
    sourceRoleAndSameObjectRetainedIsTrue :
      sourceRoleAndSameObjectRetained ≡ true

    citationImportsProof : Bool
    citationImportsProofIsFalse : citationImportsProof ≡ false

    citationCreatesAuthority : Bool
    citationCreatesAuthorityIsFalse : citationCreatesAuthority ≡ false

    acquisitionOrderEqualsPaymentOrder : Bool
    acquisitionOrderEqualsPaymentOrderIsFalse :
      acquisitionOrderEqualsPaymentOrder ≡ false

    downstreamPaymentMaySkipUnpaidDependency : Bool
    downstreamPaymentMaySkipUnpaidDependencyIsFalse :
      downstreamPaymentMaySkipUnpaidDependency ≡ false

    contextReceiptAlonePaysParticipantAuthority : Bool
    contextReceiptAlonePaysParticipantAuthorityIsFalse :
      contextReceiptAlonePaysParticipantAuthority ≡ false

    participantAuthorityReceiptAlonePaysContextTransfer : Bool
    participantAuthorityReceiptAlonePaysContextTransferIsFalse :
      participantAuthorityReceiptAlonePaysContextTransfer ≡ false

    currentConceptualReviewAutomaticallyRequiresLocalAuthorityStudy : Bool
    currentConceptualReviewAutomaticallyRequiresLocalAuthorityStudyIsFalse :
      currentConceptualReviewAutomaticallyRequiresLocalAuthorityStudy ≡ false

    transferRuleIsAliceEmpiricalFinding : Bool
    transferRuleIsAliceEmpiricalFindingIsFalse :
      transferRuleIsAliceEmpiricalFinding ≡ false

open ParticipantGovernanceContextTransferBoundary public

canonicalParticipantGovernanceContextTransferBoundary :
  ParticipantGovernanceContextTransferBoundary
canonicalParticipantGovernanceContextTransferBoundary =
  participant-governance-context-transfer-boundary
    true refl
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl

highestAlphaParticipantGovernanceReading : String
highestAlphaParticipantGovernanceReading =
  "For a participant-governance transfer claim, canonical context generalisation and same-target-context participant authority are conjunctive obligations. Prior literature, consent, procedural ethics and the Alice corpus constrain the method but do not create local authority. The current integrative conceptual review therefore retains the transfer rule without pretending that a same-object participant study has already been performed."
