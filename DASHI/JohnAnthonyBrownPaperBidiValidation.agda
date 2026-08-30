module DASHI.JohnAnthonyBrownPaperBidiValidation where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Culture.JohnAnthonyBrownChildReligiousPowerBidiExact as Brown
import DASHI.Culture.ChildReligiousAutonomyFormationBidiExact as Formation

------------------------------------------------------------------------
-- Focused consumer root for the paper-specific BIDI owners.
-- Suggested local command:
--   agda -i . DASHI/JohnAnthonyBrownPaperBidiValidation.agda
------------------------------------------------------------------------

authorAttributionPinned :
  Brown.BrownPaperSource.author Brown.johnAnthonyBrownPaper ≡
  "John Anthony Brown"
authorAttributionPinned = Brown.johnAnthonyBrownIsAttributedAuthor

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

------------------------------------------------------------------------
-- New autonomy / reopening regression.
------------------------------------------------------------------------

sameParticipationSurfacePinned :
  Formation.publicSurface Formation.openFormationEpisode
  ≡ Formation.publicSurface Formation.closedFormationEpisode
sameParticipationSurfacePinned = refl

sameActionStillNotAutonomy :
  Formation.Autonomy.emitted Formation.Autonomy.autonomousWithdrawal
  ≡ Formation.Autonomy.emitted Formation.Autonomy.constrainedWithdrawal
sameActionStillNotAutonomy = Formation.sameActionStillDoesNotDetermineAutonomy

constrainedFormationStillNotAutonomous :
  Formation.Autonomy.Autonomous Formation.constrainedFormationAxes → ⊥
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
