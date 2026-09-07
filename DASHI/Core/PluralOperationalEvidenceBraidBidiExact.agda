module DASHI.Core.PluralOperationalEvidenceBraidBidiExact where

------------------------------------------------------------------------
-- PLURAL OPERATIONAL EVIDENCE BRAID -- BIDI
--
-- Operational closure consumes multiple epistemic strands without fusing their
-- provenance, authority, permission or obligation. Crossings require explicit
-- receipts. Agreement does not transfer authority; disagreement does not erase
-- either strand; an affected-community strand may reopen a prior institutional
-- success assessment.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Core.BraidedEvidenceTraceBidiCrossPollination2026Exact as Braid
import DASHI.Core.PluralEpistemicOperationalClosureExact as Operational
import DASHI.Core.AppendOnlyEvidenceResidualRevisionExact as Revision

------------------------------------------------------------------------
-- Canonical operational strands.
------------------------------------------------------------------------

stateReportStrand : Braid.EvidenceStrand
stateReportStrand = Braid.evidence-strand
  "operational:state-self-report"
  Braid.observationWeft
  "institutional implementation/report source"
  "institutional reporting authority only"

affectedCommunityOutcomeStrand : Braid.EvidenceStrand
affectedCommunityOutcomeStrand = Braid.evidence-strand
  "operational:affected-community-outcome"
  Braid.authorityWarp
  "affected-community outcome/authority source"
  "affected-community authority remains strand-local"

independentMonitoringStrand : Braid.EvidenceStrand
independentMonitoringStrand = Braid.evidence-strand
  "operational:independent-monitoring"
  Braid.observationWeft
  "independent monitoring/evaluation source"
  "monitoring authority bounded to its protocol and source"

correctionResponseStrand : Braid.EvidenceStrand
correctionResponseStrand = Braid.evidence-strand
  "operational:correction-response"
  Braid.obligationWarp
  "observed institutional response to correction/feedback"
  "correction-response evidence does not inherit community authority"

canonicalOperationalTrace : Braid.BraidedEvidenceTrace
canonicalOperationalTrace = Braid.braided-evidence-trace
  (stateReportStrand
    ∷ affectedCommunityOutcomeStrand
    ∷ independentMonitoringStrand
    ∷ correctionResponseStrand
    ∷ [])
  "plural operational trace: State, community, monitoring and correction-response strands retained without automatic fusion"
  true refl

operationalTraceDoesNotFuse :
  Braid.noAutomaticFusion canonicalOperationalTrace ≡ true
operationalTraceDoesNotFuse = refl

------------------------------------------------------------------------
-- Crossings: the coordination itself is receipt-bearing.
------------------------------------------------------------------------

stateCommunityComparison : Braid.BraidedCrossing stateReportStrand affectedCommunityOutcomeStrand
stateCommunityComparison = Braid.braided-crossing
  Braid.comparisonCrossing
  "comparison permitted for declared operational-justice consumer; authority remains strand-local"
  "no translation of community authority into State authorship or vice versa"
  true refl
  true refl

communityMonitoringCorroboration :
  Braid.BraidedCrossing affectedCommunityOutcomeStrand independentMonitoringStrand
communityMonitoringCorroboration = Braid.braided-crossing
  Braid.corroborationCrossing
  "corroboration may strengthen a declared consumer without merging provenance"
  "monitoring language and community-defined outcome language require explicit correspondence"
  true refl
  true refl

communityCorrectionTranslation :
  Braid.BraidedCrossing affectedCommunityOutcomeStrand correctionResponseStrand
communityCorrectionTranslation = Braid.braided-crossing
  Braid.translationCrossing
  "affected-community feedback may be translated into an institutional correction obligation"
  "translation must preserve the source community and must not claim authority transfer"
  true refl
  true refl

stateIdentityRetainedAtCommunityComparison :
  Braid.leftIdentityRetained stateCommunityComparison ≡ true
stateIdentityRetainedAtCommunityComparison = refl

communityIdentityRetainedAtStateComparison :
  Braid.rightIdentityRetained stateCommunityComparison ≡ true
communityIdentityRetainedAtStateComparison = refl

communityIdentityRetainedAtCorrectionTranslation :
  Braid.leftIdentityRetained communityCorrectionTranslation ≡ true
communityIdentityRetainedAtCorrectionTranslation = refl

------------------------------------------------------------------------
-- Operational closure coordinates consume strands but do not inherit authority.
------------------------------------------------------------------------

record OperationalStrandPayment : Set where
  constructor operational-strand-payment
  field
    coordinate : Operational.OperationalClosureCoordinate
    evidenceStrand : Braid.EvidenceStrand
    evidenceReference : String
    sourceIdentityRetained : Bool
    sourceIdentityRetainedIsTrue : sourceIdentityRetained ≡ true
    paymentAutomaticallyTransfersAuthority : Bool
    paymentAutomaticallyTransfersAuthorityIsFalse :
      paymentAutomaticallyTransfersAuthority ≡ false

open OperationalStrandPayment public

communityOutcomePaymentCandidate : OperationalStrandPayment
communityOutcomePaymentCandidate = operational-strand-payment
  Operational.communityDefinedOutcomeCoordinate
  affectedCommunityOutcomeStrand
  "candidate payment must establish the community-defined outcome required by the consumer"
  true refl
  false refl

monitoringPaymentCandidate : OperationalStrandPayment
monitoringPaymentCandidate = operational-strand-payment
  Operational.independentMonitoringCoordinate
  independentMonitoringStrand
  "candidate payment must establish independent monitoring adequate for the declared consumer"
  true refl
  false refl

correctionPaymentCandidate : OperationalStrandPayment
correctionPaymentCandidate = operational-strand-payment
  Operational.correctionResponseCoordinate
  correctionResponseStrand
  "candidate payment must show that correction can alter realised operation, not merely that feedback was recorded"
  true refl
  false refl

------------------------------------------------------------------------
-- Reopening semantics.
------------------------------------------------------------------------

record BraidedReopeningBoundary : Set where
  constructor braided-reopening-boundary
  field
    laterCommunityEvidenceMayReopenStateSuccessAssessment : Bool
    laterCommunityEvidenceMayReopenStateSuccessAssessmentIsTrue :
      laterCommunityEvidenceMayReopenStateSuccessAssessment ≡ true
    reopeningRequiresDeletingEarlierStateEvidence : Bool
    reopeningRequiresDeletingEarlierStateEvidenceIsFalse :
      reopeningRequiresDeletingEarlierStateEvidence ≡ false
    disagreementRequiresChoosingOneUniversalEpistemicAuthority : Bool
    disagreementRequiresChoosingOneUniversalEpistemicAuthorityIsFalse :
      disagreementRequiresChoosingOneUniversalEpistemicAuthority ≡ false
    corroborationFusesProvenance : Bool
    corroborationFusesProvenanceIsFalse : corroborationFusesProvenance ≡ false
    translationTransfersCommunityAuthorityToInstitution : Bool
    translationTransfersCommunityAuthorityToInstitutionIsFalse :
      translationTransfersCommunityAuthorityToInstitution ≡ false

open BraidedReopeningBoundary public

canonicalBraidedReopeningBoundary : BraidedReopeningBoundary
canonicalBraidedReopeningBoundary = braided-reopening-boundary
  true refl
  false refl
  false refl
  false refl
  false refl

appendOnlyRevisionBoundary : Revision.AppendOnlyEvidenceRevisionBoundary
appendOnlyRevisionBoundary = Revision.canonicalAppendOnlyEvidenceRevisionBoundary

oldEvidenceMayPersistAcrossReopening :
  Revision.oldEvidenceMayRemainValidWhileConsumerConclusionChanges
    appendOnlyRevisionBoundary ≡ true
oldEvidenceMayPersistAcrossReopening = refl

------------------------------------------------------------------------
-- No-collapse laws inherited in a directly usable form.
------------------------------------------------------------------------

data StateReportAbsorbsCommunityAuthority : Set where
data CorroborationMakesSourcesIdentical : Set where
data TranslationMakesInstitutionCommunityAuthor : Set where
data DisagreementInvalidatesBothStrands : Set where
data MonitoringAloneClosesCommunityAuthority : Set where

stateReportDoesNotAbsorbCommunityAuthority : StateReportAbsorbsCommunityAuthority → ⊥
stateReportDoesNotAbsorbCommunityAuthority ()

corroborationDoesNotMakeSourcesIdentical : CorroborationMakesSourcesIdentical → ⊥
corroborationDoesNotMakeSourcesIdentical ()

translationDoesNotMakeInstitutionCommunityAuthor : TranslationMakesInstitutionCommunityAuthor → ⊥
translationDoesNotMakeInstitutionCommunityAuthor ()

disagreementDoesNotInvalidateBothStrands : DisagreementInvalidatesBothStrands → ⊥
disagreementDoesNotInvalidateBothStrands ()

monitoringAloneDoesNotCloseCommunityAuthority : MonitoringAloneClosesCommunityAuthority → ⊥
monitoringAloneDoesNotCloseCommunityAuthority ()
