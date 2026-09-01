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

------------------------------------------------------------------------
-- Canonical BIDI campaign order.
--
-- This is not a claim that every document must resolve every axis.  It is the
-- dependency order for any axis that a consumer actually requires.
------------------------------------------------------------------------

data BidiCampaign : Set where
  attributionPropositionCampaign : BidiCampaign
  occurrenceCampaign : BidiCampaign
  antecedentIdentityCampaign : BidiCampaign
  scopeCompositionCampaign : BidiCampaign
  participantLegalRoleCampaign : BidiCampaign
  legalApplicabilityCampaign : BidiCampaign
  documentWorldContextCampaign : BidiCampaign

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

allCampaignTypeOwnersPresent :
  campaignReadiness attributionPropositionCampaign ≡ typeOwnerPresent
allCampaignTypeOwnersPresent = refl

------------------------------------------------------------------------
-- Existing constitutional boundaries still govern every campaign.
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

------------------------------------------------------------------------
-- Campaign-specific owner witnesses in the dependency graph.
------------------------------------------------------------------------

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

------------------------------------------------------------------------
-- Completion semantics: type-level campaign availability does not claim that
-- runtime producers or governed closure receipts have been supplied for a
-- concrete corpus.
------------------------------------------------------------------------

data TypeOwnerPresenceMeansCorpusResolved : Set where
\data AggregateImportMeansKernelValidated : Set where

typeOwnersDoNotResolveCorpus : TypeOwnerPresenceMeansCorpusResolved → ⊥
typeOwnersDoNotResolveCorpus ()

aggregateImportDoesNotClaimKernelValidation : AggregateImportMeansKernelValidated → ⊥
aggregateImportDoesNotClaimKernelValidation ()
