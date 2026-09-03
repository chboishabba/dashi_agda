module DASHI.Cognition.PNF.SensibLawSemanticBidiCampaignEverything where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Cognition.PNF.SensibLawSpacyCompositionOnlySemanticConstitutionExact as Constitution
import DASHI.Cognition.PNF.SensibLawSemanticStatusProductExact as Status
import DASHI.Cognition.PNF.SensibLawSemanticStatusCrossPollinationExact as Cross
import DASHI.Cognition.PNF.SensibLawAttributionPropositionOccurrenceBidiExact as Attribution
import DASHI.Cognition.PNF.SensibLawAntecedentIdentityRefinementBidiExact as Identity
import DASHI.Cognition.PNF.SensibLawScopeCompositionBidiExact as Scope
import DASHI.Cognition.PNF.SensibLawParticipantLegalRoleWrongTypeBidiExact as LegalRole
import DASHI.Cognition.PNF.SensibLawWrongTypeApplicabilityLiabilityRemedyBidiExact as LegalChain
import DASHI.Cognition.PNF.SensibLawDocumentWorldSemanticStatusBidiExact as Context
import DASHI.Cognition.PNF.SensibLawConsumerQuerySemanticCoordinateReopeningExact as Demand
import DASHI.Cognition.PNF.SensibLawSemanticLiveVerticalEverything as Live

data BidiCampaign : Set where
  attributionPropositionCampaign : BidiCampaign
  occurrenceCampaign : BidiCampaign
  antecedentIdentityCampaign : BidiCampaign
  scopeCompositionCampaign : BidiCampaign
  participantLegalRoleCampaign : BidiCampaign
  legalApplicabilityCampaign : BidiCampaign
  documentWorldContextCampaign : BidiCampaign
  consumerQueryDemandCampaign : BidiCampaign

data CampaignReadiness : Set where
  typeOwnerPresent runtimeProducerNeeded consumerMaySkip : CampaignReadiness

campaignReadiness : BidiCampaign → CampaignReadiness
campaignReadiness attributionPropositionCampaign = typeOwnerPresent
campaignReadiness occurrenceCampaign = typeOwnerPresent
campaignReadiness antecedentIdentityCampaign = typeOwnerPresent
campaignReadiness scopeCompositionCampaign = typeOwnerPresent
campaignReadiness participantLegalRoleCampaign = typeOwnerPresent
campaignReadiness legalApplicabilityCampaign = typeOwnerPresent
campaignReadiness documentWorldContextCampaign = typeOwnerPresent
campaignReadiness consumerQueryDemandCampaign = typeOwnerPresent

allCampaignTypeOwnersPresent :
  campaignReadiness attributionPropositionCampaign ≡ typeOwnerPresent
allCampaignTypeOwnersPresent = refl

consumerQueryDemandOwnerPresent :
  campaignReadiness consumerQueryDemandCampaign ≡ typeOwnerPresent
consumerQueryDemandOwnerPresent = refl

------------------------------------------------------------------------
-- Phase transition: the aggregate also imports actual inhabited regressions.
-- This does not make the corpus resolved.
------------------------------------------------------------------------

claimDiscourseHasLiveInhabitant :
  Live.liveCampaignState Live.claimDiscourseLive ≡ Live.inhabitedRegression
claimDiscourseHasLiveInhabitant = refl

occurrenceHasLiveInhabitant :
  Live.liveCampaignState Live.occurrenceLive ≡ Live.inhabitedRegression
occurrenceHasLiveInhabitant = refl

identityRefinementHasLiveInhabitant :
  Live.liveCampaignState Live.identityRefinementLive ≡ Live.inhabitedRegression
identityRefinementHasLiveInhabitant = refl

scopeCompositionHasLiveInhabitant :
  Live.liveCampaignState Live.scopeCompositionLive ≡ Live.inhabitedRegression
scopeCompositionHasLiveInhabitant = refl

documentContextHasLiveInhabitant :
  Live.liveCampaignState Live.documentContextLive ≡ Live.inhabitedRegression
documentContextHasLiveInhabitant = refl

participantLegalRoleHasLiveInhabitant :
  Live.liveCampaignState Live.participantLegalRoleLive ≡ Live.inhabitedRegression
participantLegalRoleHasLiveInhabitant = refl

narrativeLegalGateHasLiveInhabitant :
  Live.liveCampaignState Live.narrativeLegalGateLive ≡ Live.inhabitedRegression
narrativeLegalGateHasLiveInhabitant = refl

------------------------------------------------------------------------
-- Consumer/query least-privilege boundaries are now part of the campaign root.
------------------------------------------------------------------------

legalConsumerDoesNotImplyFullApplicabilityStack :
  Demand.LegalConsumerAlwaysNeedsApplicability → ⊥
legalConsumerDoesNotImplyFullApplicabilityStack =
  Demand.legalConsumerDoesNotAlwaysNeedApplicability

unrequestedCoordinatesDoNotBlockConsumer :
  Demand.UnrequestedCoordinateMustResolve → ⊥
unrequestedCoordinatesDoNotBlockConsumer =
  Demand.unrequestedCoordinateDoesNotCountAsFailure

authorityUpdateDoesNotReparseSyntax :
  Demand.AuthorityChangeReparsesSyntax → ⊥
authorityUpdateDoesNotReparseSyntax =
  Demand.authorityChangeDoesNotReparseSyntax

broaderDemandPreservesSemanticCarrier :
  Demand.BroaderDemandRewritesSemanticCarrier → ⊥
broaderDemandPreservesSemanticCarrier =
  Demand.broaderDemandDoesNotRewriteCarrier

------------------------------------------------------------------------
-- Existing cross-axis boundaries.
------------------------------------------------------------------------

regexStillForbidden :
  Constitution.regexMayProduceSemanticEvidence
    Constitution.canonicalCompositionOnlyBoundary ≡ false
regexStillForbidden = refl

candidateStillNeedsContext :
  Constitution.semanticResolutionRequiresContextReceipt
    Constitution.canonicalCompositionOnlyBoundary ≡ true
candidateStillNeedsContext = refl

assertionStillNotTruth : Status.AssertionDeterminesTruth → ⊥
assertionStillNotTruth = Status.assertionDoesNotDetermineTruth

mentionStillNotOccurrence : Status.MentionDeterminesOccurrence → ⊥
mentionStillNotOccurrence = Status.mentionDoesNotDetermineOccurrence

agentStillNotDutyBearer : Status.LinguisticAgentDeterminesDutyBearer → ⊥
agentStillNotDutyBearer = Status.linguisticAgentDoesNotDetermineDutyBearer

applicabilityStillNotViolation : Status.ApplicabilityDeterminesViolation → ⊥
applicabilityStillNotViolation = Status.applicabilityDoesNotDetermineViolation

violationStillNotLiability : Status.ViolationDeterminesLiability → ⊥
violationStillNotLiability = Status.violationDoesNotDetermineLiability

consumerEquivalenceStillNotWorldIdentity :
  Context.ConsumerEquivalentMeansSameSemanticWorld → ⊥
consumerEquivalenceStillNotWorldIdentity = Context.consumerEquivalenceDoesNotIdentifyWorld

claimAssertionBoundary : Attribution.ClaimAssertionIsTruthProof → ⊥
claimAssertionBoundary = Attribution.claimAssertionDoesNotProveTruth

antecedentIdentityBoundary :
  Identity.UniqueAntecedentAutomaticallyClosesIdentity → ⊥
antecedentIdentityBoundary = Identity.uniqueAntecedentDoesNotAutoCloseIdentity

scopeTruthBoundary : Scope.ScopeResolutionProvesTruth → ⊥
scopeTruthBoundary = Scope.scopeResolutionDoesNotProveTruth

legalRoleBoundary : LegalRole.AgentAutomaticallyDutyBearer → ⊥
legalRoleBoundary = LegalRole.agentDoesNotAutoBecomeDutyBearer

legalChainBoundary : LegalChain.ApplicableAutomaticallyViolated → ⊥
legalChainBoundary = LegalChain.applicabilityDoesNotAutoViolate

data TypeOwnerPresenceMeansCorpusResolved : Set where
data AggregateImportMeansKernelValidated : Set where

typeOwnersDoNotResolveCorpus : TypeOwnerPresenceMeansCorpusResolved → ⊥
typeOwnersDoNotResolveCorpus ()

aggregateImportDoesNotClaimKernelValidation : AggregateImportMeansKernelValidated → ⊥
aggregateImportDoesNotClaimKernelValidation ()
