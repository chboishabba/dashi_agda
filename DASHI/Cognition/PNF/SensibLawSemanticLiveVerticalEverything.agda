module DASHI.Cognition.PNF.SensibLawSemanticLiveVerticalEverything where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Cognition.PNF.SensibLawSemanticStatusProductExact as Status
import DASHI.Cognition.PNF.SensibLawClaimLatticeNarrativeStatusLiveBidiExact as Claims
import DASHI.Cognition.PNF.SensibLawNarrativeEvidenceConsumerStatusBidiExact as Evidence
import DASHI.Cognition.PNF.SensibLawClaimAtomOntologyVerticalSliceExact as Vertical
import DASHI.Cognition.PNF.SensibLawSemanticResidualIdentityLiveBidiExact as Identity
import DASHI.Cognition.PNF.SensibLawMaterialisedSpacyReferencePopulationLiveExact as Reference
import DASHI.Cognition.PNF.SensibLawScopeCompositionLiveRegressionExact as Scope
import DASHI.Cognition.PNF.SensibLawDocumentDiscourseContextRefinementExact as Context
import DASHI.Cognition.PNF.SensibLawDocumentDiscourseLiveVerticalExact as Document
import DASHI.Cognition.PNF.SensibLawParticipantLegalRoleLiveBidiExact as LegalRole
import DASHI.Cognition.PNF.SensibLawNarrativeToLegalGateLiveBidiExact as LegalGate
import DASHI.Cognition.PNF.SensibLawWrongTypeApplicabilityLiabilityRemedyBidiExact as LegalChain
import DASHI.Cognition.PNF.SensibLawDocumentWorldSemanticStatusBidiExact as World

------------------------------------------------------------------------
-- LIVE PHASE-C/D AGGREGATE
--
-- Unlike SensibLawSemanticBidiCampaignEverything, which records type-owner
-- availability, this root imports actual inhabited regressions from existing
-- repo producers.  It still does not claim corpus coverage or kernel validation.
------------------------------------------------------------------------

data LiveCampaign : Set where
  claimDiscourseLive : LiveCampaign
  occurrenceLive : LiveCampaign
  evidenceLineageLive : LiveCampaign
  crossCarrierClaimLive : LiveCampaign
  identityRefinementLive : LiveCampaign
  referencePopulationLive : LiveCampaign
  scopeCompositionLive : LiveCampaign
  documentContextLive : LiveCampaign
  participantLegalRoleLive : LiveCampaign
  narrativeLegalGateLive : LiveCampaign

data LiveCampaignState : Set where
  inhabitedRegression : LiveCampaignState
  typeOnly : LiveCampaignState

liveCampaignState : LiveCampaign → LiveCampaignState
liveCampaignState claimDiscourseLive = inhabitedRegression
liveCampaignState occurrenceLive = inhabitedRegression
liveCampaignState evidenceLineageLive = inhabitedRegression
liveCampaignState crossCarrierClaimLive = inhabitedRegression
liveCampaignState identityRefinementLive = inhabitedRegression
liveCampaignState referencePopulationLive = inhabitedRegression
liveCampaignState scopeCompositionLive = inhabitedRegression
liveCampaignState documentContextLive = inhabitedRegression
liveCampaignState participantLegalRoleLive = inhabitedRegression
liveCampaignState narrativeLegalGateLive = inhabitedRegression

------------------------------------------------------------------------
-- Narrative status is now inhabited, not merely enumerated.
------------------------------------------------------------------------

positiveClaimIsAssertedOccurrence :
  Status.resultingOccurrenceStatus
    (Vertical.CrossCarrierOccurrenceReceipt.occurrenceResolution
      Vertical.dogWalkedOccurrenceLive)
  ≡ Status.assertedOccurrence
positiveClaimIsAssertedOccurrence = refl

denialIsDeniedOccurrence :
  Status.resultingOccurrenceStatus
    (Vertical.CrossCarrierOccurrenceReceipt.occurrenceResolution
      Vertical.dogDeniedOccurrenceLive)
  ≡ Status.deniedOccurrence
denialIsDeniedOccurrence = refl

claimTruthStillUnresolved :
  Status.resultingTruthStatus
    (Vertical.CrossCarrierPropositionReceipt.resolution
      Vertical.dogWalkedPropositionLive)
  ≡ Status.truthUnresolved
claimTruthStillUnresolved = refl

------------------------------------------------------------------------
-- Evidence/provenance and institutional planes do not overwrite truth.
------------------------------------------------------------------------

consumerDispositionTruthStillUnresolved :
  Status.truthStatus
    (Evidence.ConsumerStatusProjectionReceipt.proposition
      Evidence.notLikeUsConsumerStatus)
  ≡ Status.truthUnresolved
consumerDispositionTruthStillUnresolved = refl

repetitionStillNotTruthAuthority :
  Evidence.RepetitionRaisesTruthAuthority → ⊥
repetitionStillNotTruthAuthority = Evidence.repetitionDoesNotRaiseTruthAuthority

------------------------------------------------------------------------
-- Identity live refinement and materialised parser reference population.
------------------------------------------------------------------------

identityLiveStatus : Status.IdentityStatus
identityLiveStatus = Status.identityStatus Identity.exampleSubject

identityCoarseQueryNotRetroactivelyUnique :
  Identity.LaterProvenanceMakesCoarseQueryUnique → ⊥
identityCoarseQueryNotRetroactivelyUnique = Identity.laterProvenanceDoesNotRewriteCoarseQuery

materialisedReferencePopulationLeavesIdentityOpen :
  Status.identityStatus
    (Reference.semanticSubject Reference.canonicalMaterialisedReferencePopulation)
  ≡ Status.identityUnresolved
materialisedReferencePopulationLeavesIdentityOpen = refl

materialisedReferencePopulationCreatesAntecedentFibre :
  Status.antecedentStatus
    (Reference.semanticSubject Reference.canonicalMaterialisedReferencePopulation)
  ≡ Status.antecedentCandidateSet
materialisedReferencePopulationCreatesAntecedentFibre = refl

sameSentenceStillNotCoreferenceProof :
  Reference.SameSentenceProvesCoreference → ⊥
sameSentenceStillNotCoreferenceProof = Reference.sameSentenceDoesNotProveCoreference

------------------------------------------------------------------------
-- Scope composition is an inhabited parser-to-status chain.
------------------------------------------------------------------------

scopeParserAdmissionStillNotSemanticResolution :
  Scope.ParserAdmissionIsModalResolution → ⊥
scopeParserAdmissionStillNotSemanticResolution =
  Scope.parserAdmissionDoesNotResolveModalForce

scopeResolutionStillNotOccurrenceAdmission :
  Scope.ResolvedScopeIsOccurrenceAdmission → ⊥
scopeResolutionStillNotOccurrenceAdmission =
  Scope.resolvedScopeDoesNotAdmitOccurrence

------------------------------------------------------------------------
-- Typed document context refines discourse status without rewriting truth.
------------------------------------------------------------------------

submissionTruthStillUnresolved :
  Status.truthStatus
    (Context.ContextualPropositionRefinement.refined Document.submissionRefinement)
  ≡ Status.truthUnresolved
submissionTruthStillUnresolved = refl

findingTruthStillUnresolved :
  Status.truthStatus
    (Context.ContextualPropositionRefinement.refined Document.findingRefinement)
  ≡ Status.truthUnresolved
findingTruthStillUnresolved = refl

findingOccurrenceRequiresReceipt :
  Status.occurrence Document.establishedEventFromFinding
  ≡ Status.occurrenceAdmitted
findingOccurrenceRequiresReceipt = refl

------------------------------------------------------------------------
-- Generic Agent survives explicit, system-relative legal-role projection.
------------------------------------------------------------------------

agentFixtureDoesNotGeneraliseToAllAgents :
  LegalRole.FixtureDutyBearerMakesAllAgentsDutyBearers → ⊥
agentFixtureDoesNotGeneraliseToAllAgents =
  LegalRole.fixtureDoesNotGeneraliseAgentToDutyBearer

crossSystemRoleDifferenceRemainsValid :
  LegalRole.CrossSystemRoleDifferenceIsContradiction → ⊥
crossSystemRoleDifferenceRemainsValid =
  LegalRole.crossSystemDifferenceIsNotContradiction

------------------------------------------------------------------------
-- Narrative -> legal gate is now fail-closed on occurrence/proposition status.
------------------------------------------------------------------------

allegationOnlyCandidateLegalUse :
  LegalChain.SemanticLegalInputGate.resultingApplicability
    LegalGate.allegedCandidateGate
  ≡ Status.applicabilityCandidate
allegationOnlyCandidateLegalUse = refl

assertionOnlyCandidateLegalUse :
  LegalChain.SemanticLegalInputGate.resultingApplicability
    LegalGate.assertedCandidateGate
  ≡ Status.applicabilityCandidate
assertionOnlyCandidateLegalUse = refl

denialOnlyCandidateLegalUse :
  LegalChain.SemanticLegalInputGate.resultingApplicability
    LegalGate.deniedCandidateGate
  ≡ Status.applicabilityCandidate
denialOnlyCandidateLegalUse = refl

findingMayEnterAdmittedLegalUse :
  LegalChain.SemanticLegalInputGate.resultingApplicability
    LegalGate.findingEstablishedGate
  ≡ Status.applicabilityAdmitted
findingMayEnterAdmittedLegalUse = refl

findingLegalUseStillNotUniversalTruth :
  Status.truthStatus LegalGate.foundPropositionStatus ≡ Status.truthUnresolved
findingLegalUseStillNotUniversalTruth = refl

------------------------------------------------------------------------
-- Existing document/world boundaries remain in force.
------------------------------------------------------------------------

worldConsumerEquivalenceStillNotIdentity :
  World.ConsumerEquivalentMeansSameSemanticWorld → ⊥
worldConsumerEquivalenceStillNotIdentity = World.consumerEquivalenceDoesNotIdentifyWorld

------------------------------------------------------------------------
-- Completion boundaries.
------------------------------------------------------------------------

data LiveRegressionMeansCorpusCoverage : Set where
data LiveRegressionMeansKernelValidated : Set where
data LiveNarrativeStatusMeansLegalConclusion : Set where

liveRegressionDoesNotMeanCorpusCoverage : LiveRegressionMeansCorpusCoverage → ⊥
liveRegressionDoesNotMeanCorpusCoverage ()

liveRegressionDoesNotMeanKernelValidation : LiveRegressionMeansKernelValidated → ⊥
liveRegressionDoesNotMeanKernelValidation ()

liveNarrativeStatusDoesNotMeanLegalConclusion :
  LiveNarrativeStatusMeansLegalConclusion → ⊥
liveNarrativeStatusDoesNotMeanLegalConclusion ()
