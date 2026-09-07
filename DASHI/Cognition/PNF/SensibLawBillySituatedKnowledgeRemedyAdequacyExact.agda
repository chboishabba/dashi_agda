module DASHI.Cognition.PNF.SensibLawBillySituatedKnowledgeRemedyAdequacyExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Culture.IndigenousKnowledgeStoryTwoEyedSeeingBidiExact as Knowledge
import DASHI.Culture.KimmererTwoEyedSeeingInterpretationBoundaryExact as TwoEyed
import DASHI.Cognition.PNF.SensibLawBillyEffectiveRemedyTwoEyedSeeingExact as Billy
import DASHI.Cognition.PNF.SensibLawJuridicalPersonhoodRemedyOperationalCrossPollinationExact as Operational
import DASHI.Cognition.PNF.SensibLawDeclaredReasonRealizedEffectOperationalExact as Realized

------------------------------------------------------------------------
-- BILLY REMEDY / SITUATED KNOWLEDGE ADEQUACY
--
-- Australian/Torres Strait remedy design must not be reduced to an extracted
-- proposition or a generic "consultation happened" observable.  The imported
-- Indigenous-knowledge owner already proves that identical extracted content
-- can coexist with distinct provenance, authority, permission and obligation.
-- This file transports that structural result into remedy adequacy only; it
-- does not claim every Indigenous nation shares one knowledge protocol.
------------------------------------------------------------------------

data RemedyKnowledgeCoordinate : Set where
  contentHeard : RemedyKnowledgeCoordinate
  placeRelationPreserved : RemedyKnowledgeCoordinate
  communityRelationPreserved : RemedyKnowledgeCoordinate
  provenancePreserved : RemedyKnowledgeCoordinate
  communityAuthorityPreserved : RemedyKnowledgeCoordinate
  permissionProtocolPreserved : RemedyKnowledgeCoordinate
  reciprocalObligationPreserved : RemedyKnowledgeCoordinate
  implementationFeedbackClosed : RemedyKnowledgeCoordinate


data CoordinateRequirement : Set where
  requiredForAdequacy : CoordinateRequirement
  usefulButNotSufficient : CoordinateRequirement
  sourceSpecific : CoordinateRequirement


requirement : RemedyKnowledgeCoordinate → CoordinateRequirement
requirement contentHeard = usefulButNotSufficient
requirement placeRelationPreserved = requiredForAdequacy
requirement communityRelationPreserved = requiredForAdequacy
requirement provenancePreserved = requiredForAdequacy
requirement communityAuthorityPreserved = requiredForAdequacy
requirement permissionProtocolPreserved = requiredForAdequacy
requirement reciprocalObligationPreserved = requiredForAdequacy
requirement implementationFeedbackClosed = requiredForAdequacy

contentAloneIsNotSufficient : requirement contentHeard ≡ usefulButNotSufficient
contentAloneIsNotSufficient = refl

communityAuthorityIsRequired :
  requirement communityAuthorityPreserved ≡ requiredForAdequacy
communityAuthorityIsRequired = refl

reciprocalObligationIsRequired :
  requirement reciprocalObligationPreserved ≡ requiredForAdequacy
reciprocalObligationIsRequired = refl

------------------------------------------------------------------------
-- Reuse the exact non-factorability results from the knowledge carrier.
------------------------------------------------------------------------

sameContentCannotRecoverProvenance :
  INF.FactorsThrough Knowledge.extractedProposition Knowledge.carrierProvenance → ⊥
sameContentCannotRecoverProvenance = Knowledge.propositionCannotRecoverProvenance

sameContentCannotRecoverAuthority :
  INF.FactorsThrough Knowledge.extractedProposition Knowledge.authority → ⊥
sameContentCannotRecoverAuthority = Knowledge.propositionCannotRecoverAuthority

sameContentCannotRecoverPermission :
  INF.FactorsThrough Knowledge.extractedProposition Knowledge.permission → ⊥
sameContentCannotRecoverPermission = Knowledge.propositionCannotRecoverPermission

sameContentCannotRecoverObligation :
  INF.FactorsThrough Knowledge.extractedProposition Knowledge.obligation → ⊥
sameContentCannotRecoverObligation = Knowledge.propositionCannotRecoverObligation

------------------------------------------------------------------------
-- Consultation surface != authority-bearing participation.
------------------------------------------------------------------------

data ConsultationSurfaceState : Set where
  sameStatementExtractedAuthorityIgnored : ConsultationSurfaceState
  sameStatementExtractedAuthorityPreserved : ConsultationSurfaceState


data ConsultationSurface : Set where
  statementRecorded : ConsultationSurface

data AuthorityBearingParticipation : Set where
  authorityErased : AuthorityBearingParticipation
  authorityPreserved : AuthorityBearingParticipation

data ReciprocalImplementation : Set where
  oneWayExtraction : ReciprocalImplementation
  reciprocalFeedback : ReciprocalImplementation

consultationSurface : ConsultationSurfaceState → ConsultationSurface
consultationSurface _ = statementRecorded

authorityParticipation : ConsultationSurfaceState → AuthorityBearingParticipation
authorityParticipation sameStatementExtractedAuthorityIgnored = authorityErased
authorityParticipation sameStatementExtractedAuthorityPreserved = authorityPreserved

reciprocalImplementation : ConsultationSurfaceState → ReciprocalImplementation
reciprocalImplementation sameStatementExtractedAuthorityIgnored = oneWayExtraction
reciprocalImplementation sameStatementExtractedAuthorityPreserved = reciprocalFeedback

authorityDiffers :
  authorityParticipation sameStatementExtractedAuthorityIgnored
  ≡ authorityParticipation sameStatementExtractedAuthorityPreserved → ⊥
authorityDiffers ()

reciprocityDiffers :
  reciprocalImplementation sameStatementExtractedAuthorityIgnored
  ≡ reciprocalImplementation sameStatementExtractedAuthorityPreserved → ⊥
reciprocityDiffers ()

consultationAuthorityWitness :
  INF.NonFactorabilityWitness consultationSurface authorityParticipation
consultationAuthorityWitness = INF.nonFactorabilityWitness
  sameStatementExtractedAuthorityIgnored
  sameStatementExtractedAuthorityPreserved
  refl
  authorityDiffers

consultationReciprocityWitness :
  INF.NonFactorabilityWitness consultationSurface reciprocalImplementation
consultationReciprocityWitness = INF.nonFactorabilityWitness
  sameStatementExtractedAuthorityIgnored
  sameStatementExtractedAuthorityPreserved
  refl
  reciprocityDiffers

consultationRecordCannotRecoverAuthorityParticipation :
  INF.FactorsThrough consultationSurface authorityParticipation → ⊥
consultationRecordCannotRecoverAuthorityParticipation =
  INF.witnessRulesOutEveryFlatFactorisation consultationAuthorityWitness

consultationRecordCannotRecoverReciprocalImplementation :
  INF.FactorsThrough consultationSurface reciprocalImplementation → ⊥
consultationRecordCannotRecoverReciprocalImplementation =
  INF.witnessRulesOutEveryFlatFactorisation consultationReciprocityWitness

------------------------------------------------------------------------
-- Billy coordinate weld.
------------------------------------------------------------------------

record BillyMeaningfulConsultationAdequacy : Set where
  constructor billy-meaningful-consultation-adequacy
  field
    committeeCoordinate : Billy.RemedyCoordinate
    sourceState : Billy.PublicImplementationState
    consultationEventCountSufficient : Bool
    consultationEventCountSufficientIsFalse : consultationEventCountSufficient ≡ false
    communityDefinedNeedsRequired : Bool
    communityDefinedNeedsRequiredIsTrue : communityDefinedNeedsRequired ≡ true
    communityAuthorityRequired : Bool
    communityAuthorityRequiredIsTrue : communityAuthorityRequired ≡ true
    knowledgeProvenanceRequired : Bool
    knowledgeProvenanceRequiredIsTrue : knowledgeProvenanceRequired ≡ true
    permissionAndProtocolRequired : Bool
    permissionAndProtocolRequiredIsTrue : permissionAndProtocolRequired ≡ true
    reciprocalFeedbackRequired : Bool
    reciprocalFeedbackRequiredIsTrue : reciprocalFeedbackRequired ≡ true
    adequacyReading : String

open BillyMeaningfulConsultationAdequacy public

canonicalBillyMeaningfulConsultationAdequacy : BillyMeaningfulConsultationAdequacy
canonicalBillyMeaningfulConsultationAdequacy = billy-meaningful-consultation-adequacy
  Billy.meaningfulConsultation
  (Billy.publicImplementationState Billy.meaningfulConsultation)
  false refl
  true refl
  true refl
  true refl
  true refl
  true refl
  "The public existence of consultation is evidence of activity, not by itself evidence that the Committee's meaningful-consultation/full-reparation requirement is satisfied. Adequacy must retain community-defined needs, authority, provenance, protocol and an iterative feedback path into implementation."

------------------------------------------------------------------------
-- Two-Eyed Seeing remains coordination, not state absorption of knowledge.
------------------------------------------------------------------------

twoEyedCoordinationDoesNotFuseHistories :
  TwoEyed.coordinatedUseRequiresEpistemicFusion
    TwoEyed.canonicalKimmererTwoEyedSeeingBoundary ≡ false
twoEyedCoordinationDoesNotFuseHistories = refl

sharedObservationDoesNotRecoverProvenance :
  INF.FactorsThrough TwoEyed.observeKnowledgeHistory TwoEyed.provenance → ⊥
sharedObservationDoesNotRecoverProvenance = TwoEyed.sharedObservationDoesNotRecoverProvenance

------------------------------------------------------------------------
-- Operational closure x-pollination.
------------------------------------------------------------------------

consultationAndFundingStillDoNotEqualFullReparation :
  Operational.ConsultationAndFundingMeanFullReparationCompleted → ⊥
consultationAndFundingStillDoNotEqualFullReparation = Operational.activityDoesNotEqualFullReparation

stateMetricDoesNotDetermineCommunityRemedyAdequacy :
  Realized.stateDefinedMetricAloneDeterminesCommunityRemedyAdequacy
    Realized.canonicalCommunityDefinedOutcomeBoundary ≡ false
stateMetricDoesNotDetermineCommunityRemedyAdequacy = refl

correctionFeedbackIsPartOfOperationalAssessment :
  Realized.correctionFeedbackIsPartOfSystemOperation
    Realized.canonicalCommunityDefinedOutcomeBoundary ≡ true
correctionFeedbackIsPartOfOperationalAssessment = refl

------------------------------------------------------------------------
-- No-collapse laws.
------------------------------------------------------------------------

data StatementRecordedMeansAuthorityPreserved : Set where
data GovernmentConsultationCreatesCommunityAuthority : Set where
data ScientificConvergenceMeansKnowledgeFusion : Set where
data AustralianFixtureMeansUniversalIndigenousEpistemology : Set where

recordedStatementDoesNotProveAuthorityPreserved :
  StatementRecordedMeansAuthorityPreserved → ⊥
recordedStatementDoesNotProveAuthorityPreserved ()

consultationDoesNotCreateCommunityAuthority :
  GovernmentConsultationCreatesCommunityAuthority → ⊥
consultationDoesNotCreateCommunityAuthority ()

convergenceDoesNotFuseKnowledge : ScientificConvergenceMeansKnowledgeFusion → ⊥
convergenceDoesNotFuseKnowledge ()

australianFixtureDoesNotUniversalizeIndigenousKnowledge :
  AustralianFixtureMeansUniversalIndigenousEpistemology → ⊥
australianFixtureDoesNotUniversalizeIndigenousKnowledge ()
