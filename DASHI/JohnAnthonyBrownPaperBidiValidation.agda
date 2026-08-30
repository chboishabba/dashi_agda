module DASHI.JohnAnthonyBrownPaperBidiValidation where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Cognition.PNF.DecisionAutonomyExact as Autonomy
import DASHI.Culture.JohnAnthonyBrownChildReligiousPowerBidiExact as Brown
import DASHI.Culture.JohnAnthonyBrownDocumentLineageExact as Lineage
import DASHI.Culture.JohnAnthonyBrownStudyDesignBidiExact as Design
import DASHI.Culture.JohnAnthonyBrownPaperSectionHypothesisManifestExact as Manifest
import DASHI.Culture.ChildReligiousAutonomyFormationBidiExact as Formation
import DASHI.Culture.ChildReligiousEpistemicReopeningBidiExact as Epistemic
import DASHI.Culture.ReligiousThreatPredicateDialecticBidiExact as Threat
import DASHI.Culture.ReligiousSanctionFeministWiccaCrossPollinationExact as FW

------------------------------------------------------------------------
-- Focused consumer root for the paper-specific BIDI owners.
-- Suggested local command:
--   agda -i . DASHI/JohnAnthonyBrownPaperBidiValidation.agda
------------------------------------------------------------------------

authorAttributionPinned :
  Brown.BrownPaperSource.author Brown.johnAnthonyBrownPaper ≡
  "John Anthony Brown"
authorAttributionPinned = Brown.johnAnthonyBrownIsAttributedAuthor

latestDocumentAuthorPinned :
  Lineage.BrownDocumentSnapshot.attributedAuthor Lineage.latestProposalSnapshot
  ≡ "John Anthony Brown"
latestDocumentAuthorPinned = Lineage.latestProposalAuthor

latestDocumentStagePinned :
  Lineage.BrownDocumentSnapshot.stage Lineage.latestProposalSnapshot
  ≡ Lineage.comparativeMixedMethodsProposal
latestDocumentStagePinned = Lineage.latestProposalStage

laterDraftNotAutomaticValidation :
  Lineage.LaterDraftPromotesEarlierClaimToFact → ⊥
laterDraftNotAutomaticValidation = Lineage.laterDraftDoesNotPromoteEarlierClaimToFact

driveModifierNotAuthorship : Lineage.DriveLastModifierPromotesAuthorship → ⊥
driveModifierNotAuthorship = Lineage.driveLastModifierDoesNotPromoteAuthorship

conditionalHypothesesPreserved :
  Brown.JohnAnthonyBrownPaperBidiBoundary.paperPositiveAndNegativeOutcomeHypothesesPreserved
    Brown.canonicalJohnAnthonyBrownPaperBidiBoundary
  ≡ true
conditionalHypothesesPreserved = refl

ordinaryTeachingNotEntrapment :
  Brown.JohnAnthonyBrownPaperBidiBoundary.ordinaryReligiousTeachingEqualsEntrapment
    Brown.canonicalJohnAnthonyBrownPaperBidiBoundary
  ≡ false
ordinaryTeachingNotEntrapment = refl

hellFearRemainsResearchableMechanism :
  Brown.JohnAnthonyBrownPaperBidiBoundary.hellFearMechanismMayBeResearchable
    Brown.canonicalJohnAnthonyBrownPaperBidiBoundary
  ≡ true
hellFearRemainsResearchableMechanism = refl

hellPaperForwardRoutePinned :
  Brown.BrownPaperBidiRoute.forwardObligation Brown.hellBidiRoute
  ≡ Brown.fearMechanismReceipt
hellPaperForwardRoutePinned = refl

hellFormalReturnRoutePinned :
  Brown.BrownPaperBidiRoute.backwardRevision Brown.hellBidiRoute
  ≡ Brown.splitMechanismFromOutcome
hellFormalReturnRoutePinned = refl

colonialPaperForwardRoutePinned :
  Brown.BrownPaperBidiRoute.forwardObligation Brown.colonialBidiRoute
  ≡ Brown.colonialHistoryReceipt
colonialPaperForwardRoutePinned = refl

melbourneResponseReturnRoutePinned :
  Brown.BrownPaperBidiRoute.backwardRevision Brown.melbourneResponseBidiRoute
  ≡ Brown.addIndependentInstitutionalReceipt
melbourneResponseReturnRoutePinned = refl

reverseObservationDoesNotRecoverFormation :
  Brown.FearPromotesUniqueFormationRoute → ⊥
reverseObservationDoesNotRecoverFormation = Brown.fearDoesNotPromoteUniqueFormationRoute

mechanismResemblanceNotLegalElements :
  Brown.MechanismResemblancePromotesLegalElements → ⊥
mechanismResemblanceNotLegalElements =
  Brown.mechanismResemblanceDoesNotPromoteLegalElements

psychologicalCoercionNotModernSlavery :
  Brown.PsychologicalCoercionPromotesModernSlavery → ⊥
psychologicalCoercionNotModernSlavery =
  Brown.psychologicalCoercionDoesNotPromoteModernSlavery

hardAgeSwitchNotInstalled :
  Brown.JohnAnthonyBrownPaperBidiBoundary.hardAgeThresholdInstalled
    Brown.canonicalJohnAnthonyBrownPaperBidiBoundary
  ≡ false
hardAgeSwitchNotInstalled = refl

institutionalScalesNotCollapsed :
  Brown.JohnAnthonyBrownPaperBidiBoundary.familyChurchInstitutionStateCollapsedToOneActor
    Brown.canonicalJohnAnthonyBrownPaperBidiBoundary
  ≡ false
institutionalScalesNotCollapsed = refl

formalAuditReturnsRevisionObligations :
  Brown.JohnAnthonyBrownPaperBidiBoundary.paperMayReceiveRevisionObligationsFromFormalAudit
    Brown.canonicalJohnAnthonyBrownPaperBidiBoundary
  ≡ true
formalAuditReturnsRevisionObligations = refl

studyDesignIsLongitudinalMixedMethods :
  Design.JohnAnthonyBrownStudyDesignBoundary.latestProposalUsesLongitudinalMixedMethods
    Design.canonicalJohnAnthonyBrownStudyDesignBoundary
  ≡ true
studyDesignIsLongitudinalMixedMethods = refl

retrospectiveExposureBlocksAutomaticCausation :
  Design.LongitudinalDesignPromotesCausation → ⊥
retrospectiveExposureBlocksAutomaticCausation = Design.longitudinalDoesNotPromoteCausation

adjustmentDoesNotEraseConfounding :
  Design.CovariateAdjustmentPromotesNoConfounding → ⊥
adjustmentDoesNotEraseConfounding = Design.adjustmentDoesNotPromoteNoConfounding

comparisonGroupsNotEquivalentHarms :
  Design.ComparatorPromotesEquivalentHarm → ⊥
comparisonGroupsNotEquivalentHarms = Design.comparatorDoesNotPromoteEquivalentHarm

newMeasureNeedsValidation :
  Design.JohnAnthonyBrownStudyDesignBoundary.newExposureMeasureRequiresValidation
    Design.canonicalJohnAnthonyBrownStudyDesignBoundary
  ≡ true
newMeasureNeedsValidation = refl

mixedMethodsRetainsDivergence :
  Design.MixedMethodsIntegrationReceipt.divergenceMayBeReported
    Design.canonicalMixedMethodsIntegration
  ≡ true
mixedMethodsRetainsDivergence = refl

allFiveLatestHypothesesTyped :
  Manifest.SectionHypothesisManifestBoundary.allFiveHypothesesTyped
    Manifest.canonicalSectionHypothesisManifestBoundary
  ≡ true
allFiveLatestHypothesesTyped = refl

hypothesesNotFindings :
  Manifest.SectionHypothesisManifestBoundary.hypothesesTreatedAsFindings
    Manifest.canonicalSectionHypothesisManifestBoundary
  ≡ false
hypothesesNotFindings = refl

citationsNotAutomaticallyVerified :
  Manifest.PaperCitationPromotesVerifiedSource → ⊥
citationsNotAutomaticallyVerified = Manifest.paperCitationDoesNotPromoteVerifiedSource

riskAndResilienceRemainPresent :
  Manifest.SectionHypothesisManifestBoundary.riskAndResilienceBothPreserved
    Manifest.canonicalSectionHypothesisManifestBoundary
  ≡ true
riskAndResilienceRemainPresent = refl

sameParticipationSurfacePinned :
  Formation.publicSurface Formation.openFormationEpisode
  ≡ Formation.publicSurface Formation.closedFormationEpisode
sameParticipationSurfacePinned = refl

sameActionStillNotAutonomy :
  Autonomy.emitted Autonomy.autonomousWithdrawal
  ≡ Autonomy.emitted Autonomy.constrainedWithdrawal
sameActionStillNotAutonomy = Formation.sameActionStillDoesNotDetermineAutonomy

constrainedFormationStillNotAutonomous :
  Autonomy.Autonomous Formation.constrainedFormationAxes → ⊥
constrainedFormationStillNotAutonomous = Formation.constrainedFormationNotAutonomous

laterReopeningMatters :
  Formation.ChildReligiousAutonomyFormationBoundary.laterReopeningConditionsMatter
    Formation.canonicalChildReligiousAutonomyFormationBoundary
  ≡ true
laterReopeningMatters = refl

participationNotConsent : Formation.ParticipationPromotesConsent → ⊥
participationNotConsent = Formation.participationDoesNotPromoteConsent

fearNotEntrapment : Formation.FearPromotesEntrapment → ⊥
fearNotEntrapment = Formation.fearDoesNotPromoteEntrapment

threatRepresentationNotExperiencedFear :
  Formation.ChildReligiousAutonomyFormationBoundary.threatRepresentationEqualsExperiencedFear
    Formation.canonicalChildReligiousAutonomyFormationBoundary
  ≡ false
threatRepresentationNotExperiencedFear = refl

uniqueFormationRouteStillUnrecoverable :
  Formation.ChildReligiousAutonomyFormationBoundary.observedConformityRecoversUniqueFormationRoute
    Formation.canonicalChildReligiousAutonomyFormationBoundary
  ≡ false
uniqueFormationRouteStillUnrecoverable = refl

------------------------------------------------------------------------
-- Epistemic reopening / profession regression.
------------------------------------------------------------------------

sameProfessionSurfaceDifferentEpistemicRoute :
  Epistemic.professionSurface Epistemic.revisablyEndorsed
  ≡ Epistemic.professionSurface Epistemic.inheritedClosedProfession
sameProfessionSurfaceDifferentEpistemicRoute = refl

professionNotAutonomousEndorsement :
  Epistemic.ProfessionPromotesAutonomousEndorsement → ⊥
professionNotAutonomousEndorsement =
  Epistemic.professionDoesNotPromoteAutonomousEndorsement

counterEvidenceNotSafeRevision :
  Epistemic.CounterEvidenceAccessPromotesSafeRevision → ⊥
counterEvidenceNotSafeRevision = Epistemic.counterEvidenceDoesNotPromoteSafeRevision

safeRevisionNotForcedBeliefChange :
  Epistemic.SafeRevisionPromotesBeliefChange → ⊥
safeRevisionNotForcedBeliefChange = Epistemic.safeRevisionDoesNotPromoteBeliefChange

publicProfessionDoesNotRecoverUniqueEpistemicRoute :
  Epistemic.ChildReligiousEpistemicReopeningBoundary.publicProfessionRecoversUniqueEpistemicRoute
    Epistemic.canonicalChildReligiousEpistemicReopeningBoundary
  ≡ false
publicProfessionDoesNotRecoverUniqueEpistemicRoute = refl

reopeningCanMatterWithoutBeliefChange :
  Epistemic.ChildReligiousEpistemicReopeningBoundary.reopeningCanMatterWithoutForcingBeliefChange
    Epistemic.canonicalChildReligiousEpistemicReopeningBoundary
  ≡ true
reopeningCanMatterWithoutBeliefChange = refl

inheritedBeliefMayLaterBeRevisablyEndorsed :
  Epistemic.ChildReligiousEpistemicReopeningBoundary.inheritedBeliefCanLaterBeRevisablyEndorsed
    Epistemic.canonicalChildReligiousEpistemicReopeningBoundary
  ≡ true
inheritedBeliefMayLaterBeRevisablyEndorsed = refl

------------------------------------------------------------------------
-- Predicate-normal / dialectical threat regression.
------------------------------------------------------------------------

hellThreatLiteralPinned :
  Threat.naturalLanguage Threat.hellThreatAssertion
  ≡ "If you do X, you're going to hell."
hellThreatLiteralPinned = refl

bareThreatNotPressureCandidate :
  Threat.BareUtterancePromotesPressureCandidate → ⊥
bareThreatNotPressureCandidate = Threat.bareUtteranceDoesNotPromotePressureCandidate

pressureCandidateNotEntrapment :
  Threat.PressureCandidatePromotesEntrapment → ⊥
pressureCandidateNotEntrapment = Threat.pressureCandidateDoesNotPromoteEntrapment

pressureCandidateNotLegalCoercion :
  Threat.PressureCandidatePromotesLegalCoercion → ⊥
pressureCandidateNotLegalCoercion = Threat.pressureCandidateDoesNotPromoteLegalCoercion

behaviourEffectDoesNotProveThreatTruth :
  Threat.BehaviourEffectPromotesThreatTruth → ⊥
behaviourEffectDoesNotProveThreatTruth = Threat.behaviourEffectDoesNotPromoteThreatTruth

threatTruthDoesNotProveBehaviourEffect :
  Threat.ThreatTruthPromotesBehaviourEffect → ⊥
threatTruthDoesNotProveBehaviourEffect = Threat.threatTruthDoesNotPromoteBehaviourEffect

doctrinalCounterclaimNotNegation :
  Threat.doctrinalCounterclaim ≡ Threat.logicalNegation → ⊥
doctrinalCounterclaimNotNegation = Threat.doctrinalCounterclaimNotLogicalNegation

ethicalCounterpositionNotNegation :
  Threat.logicalNegation ≡ Threat.ethicalCounterposition → ⊥
ethicalCounterpositionNotNegation = Threat.logicalNegationNotEthicalCounterposition

authorityChallengeNotNegation :
  Threat.authorityChallenge ≡ Threat.logicalNegation → ⊥
authorityChallengeNotNegation = Threat.authorityChallengeNotLogicalNegation

unresolvedThreatComponentNotRefutation :
  Threat.UnresolvedPromotesFalse → ⊥
unresolvedThreatComponentNotRefutation = Threat.unresolvedDoesNotPromoteFalse

recipientEffectNeedsSeparateReceipt :
  Threat.ReligiousThreatPredicateDialecticBoundary.recipientEffectRequiresIndependentReceipt
    Threat.canonicalReligiousThreatPredicateDialecticBoundary
  ≡ true
recipientEffectNeedsSeparateReceipt = refl

authorityProvenanceNeedsSeparateReceipt :
  Threat.ReligiousThreatPredicateDialecticBoundary.authorityProvenanceRequiresIndependentReceipt
    Threat.canonicalReligiousThreatPredicateDialecticBoundary
  ≡ true
authorityProvenanceNeedsSeparateReceipt = refl

------------------------------------------------------------------------
-- Feminist / Wicca cross-pollination regression.
------------------------------------------------------------------------

sanctionNotFeministIdentity : FW.ReligiousSanctionPromotesFeminism → ⊥
sanctionNotFeministIdentity = FW.religiousSanctionDoesNotPromoteFeminism

sanctionNotWiccanIdentity : FW.ReligiousSanctionPromotesWiccanIdentity → ⊥
sanctionNotWiccanIdentity = FW.religiousSanctionDoesNotPromoteWiccanIdentity

laterWiccanIdentityNotPriorCoercion : FW.LaterWiccanIdentityPromotesPriorCoercion → ⊥
laterWiccanIdentityNotPriorCoercion = FW.laterWiccanIdentityDoesNotPromotePriorCoercion

feministCounterpositionNotLogicalNegation :
  FW.FeministCounterpositionPromotesLogicalNegation → ⊥
feministCounterpositionNotLogicalNegation =
  FW.feministCounterpositionDoesNotPromoteLogicalNegation

wiccanReclamationNotAncientLineage : FW.WiccanReclamationPromotesAncientLineage → ⊥
wiccanReclamationNotAncientLineage = FW.wiccanReclamationDoesNotPromoteAncientLineage

counterFormationNotGuaranteedSynthesis : FW.CounterFormationPromotesSynthesis → ⊥
counterFormationNotGuaranteedSynthesis = FW.counterFormationDoesNotPromoteSynthesis

laterAlternativeSurfaceDoesNotRecoverChildhoodRoute :
  FW.ReligiousSanctionFeministWiccaBoundary.publicIdentityRecoversFormationRoute
    FW.canonicalReligiousSanctionFeministWiccaBoundary
  ≡ false
laterAlternativeSurfaceDoesNotRecoverChildhoodRoute = refl

positiveRechartingNeedsResidual :
  FW.ReligiousSanctionFeministWiccaBoundary.positiveRechartingRequiresResidualInformation
    FW.canonicalReligiousSanctionFeministWiccaBoundary
  ≡ true
positiveRechartingNeedsResidual = refl

dialecticalRoleDependsOnFrame :
  FW.ReligiousSanctionFeministWiccaBoundary.dialecticalRoleDependsOnFrame
    FW.canonicalReligiousSanctionFeministWiccaBoundary
  ≡ true
dialecticalRoleDependsOnFrame = refl
