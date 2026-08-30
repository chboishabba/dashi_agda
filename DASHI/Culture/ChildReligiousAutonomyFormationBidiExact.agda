module DASHI.Culture.ChildReligiousAutonomyFormationBidiExact where

------------------------------------------------------------------------
-- CHILD RELIGIOUS FORMATION / AUTONOMY BIDI
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Cognition.PNF.DecisionAutonomyExact as Autonomy
import DASHI.Culture.JohnAnthonyBrownChildReligiousPowerBidiExact as Brown
import DASHI.Culture.ReligiousPowerChildFearClaimBidiExact as ClaimAudit

record FormationConditions : Set where
  constructor formation-conditions
  field
    developmentalDependence : Bool
    authorityAsymmetry : Bool
    familyBelongingDependence : Bool
    cosmologicalThreatOrRewardRepresented : Bool
    independentAlternativesAccessible : Bool
    doubtPermitted : Bool
    refusalPermitted : Bool
    revisionOpportunity : Bool
    practicalExitAvailable : Bool
    subjectVoiceRecognised : Bool

open FormationConditions public

record FormationEpisode : Set where
  constructor formation-episode
  field
    conditions : FormationConditions
    autonomyAxes : Autonomy.AutonomyAxes
    publicSurface : String
    sourceRole : String

open FormationEpisode public

freeFormationAxes : Autonomy.AutonomyAxes
freeFormationAxes = Autonomy.freeAxes

constrainedFormationAxes : Autonomy.AutonomyAxes
constrainedFormationAxes = Autonomy.constrainedAxes

freeFormationAutonomous : Autonomy.Autonomous freeFormationAxes
freeFormationAutonomous = Autonomy.freeIsAutonomous

constrainedFormationNotAutonomous :
  Autonomy.Autonomous constrainedFormationAxes → ⊥
constrainedFormationNotAutonomous = Autonomy.constrainedNotAutonomous

sameActionStillDoesNotDetermineAutonomy :
  Autonomy.emitted Autonomy.autonomousWithdrawal
  ≡ Autonomy.emitted Autonomy.constrainedWithdrawal
sameActionStillDoesNotDetermineAutonomy = refl

openFormationConditions : FormationConditions
openFormationConditions = formation-conditions
  true true true true
  true true true true true true

closedFormationConditions : FormationConditions
closedFormationConditions = formation-conditions
  true true true true
  false false false false false false

openFormationEpisode : FormationEpisode
openFormationEpisode = formation-episode
  openFormationConditions
  freeFormationAxes
  "outward religious participation"
  "finite DASHI witness: participation with accessible alternatives, refusal and revision"

closedFormationEpisode : FormationEpisode
closedFormationEpisode = formation-episode
  closedFormationConditions
  constrainedFormationAxes
  "outward religious participation"
  "finite DASHI witness: same public participation under restricted alternatives/revision"

samePublicParticipationDifferentAutonomy :
  publicSurface openFormationEpisode ≡ publicSurface closedFormationEpisode
samePublicParticipationDifferentAutonomy = refl

record ReopeningReceipt : Set where
  constructor reopening-receipt
  field
    alternativesLaterAccessible : Bool
    doubtLaterPermitted : Bool
    refusalLaterPermitted : Bool
    revisionLaterPossible : Bool
    exitLaterPracticable : Bool
    subjectVoiceLaterRecognised : Bool
    provenance : String

open ReopeningReceipt public

canonicalOpenReopening : ReopeningReceipt
canonicalOpenReopening = reopening-receipt
  true true true true true true
  "finite positive reopening witness; not an empirical population estimate"

canonicalClosedReopening : ReopeningReceipt
canonicalClosedReopening = reopening-receipt
  false false false false false false
  "finite constrained reopening witness; not a claim about all religious families"

record CosmologicalThreatReceipt : Set where
  constructor cosmological-threat-receipt
  field
    threatRepresented : Bool
    childUnderstoodThreat : Bool
    fearResponseObserved : Bool
    behaviourEffectObserved : Bool
    enduringOutcomeObserved : Bool
    sourceProvenance : String

open CosmologicalThreatReceipt public

data ThreatRepresentationPromotesFear : Set where

data FearPromotesEntrapment : Set where

data FearPromotesEnduringHarm : Set where

data ParticipationPromotesConsent : Set where

data ReligiousIdentityPromotesAutonomousEndorsement : Set where

threatRepresentationDoesNotPromoteFear : ThreatRepresentationPromotesFear → ⊥
threatRepresentationDoesNotPromoteFear ()

fearDoesNotPromoteEntrapment : FearPromotesEntrapment → ⊥
fearDoesNotPromoteEntrapment ()

fearDoesNotPromoteEnduringHarm : FearPromotesEnduringHarm → ⊥
fearDoesNotPromoteEnduringHarm ()

participationDoesNotPromoteConsent : ParticipationPromotesConsent → ⊥
participationDoesNotPromoteConsent ()

religiousIdentityDoesNotPromoteAutonomousEndorsement :
  ReligiousIdentityPromotesAutonomousEndorsement → ⊥
religiousIdentityDoesNotPromoteAutonomousEndorsement ()

data RecoveryStatus : Set where
  recovered : RecoveryStatus
  bounded : RecoveryStatus
  unresolved : RecoveryStatus
  nonidentifiableFromSurface : RecoveryStatus

record FormationBackwardAudit : Set where
  constructor formation-backward-audit
  field
    publicBehaviour : RecoveryStatus
    doctrineExposure : RecoveryStatus
    experiencedFear : RecoveryStatus
    alternativeAccess : RecoveryStatus
    refusalCapacity : RecoveryStatus
    revisionOpportunityStatus : RecoveryStatus
    privateBelief : RecoveryStatus
    autonomousConsent : RecoveryStatus
    uniqueFormationRoute : RecoveryStatus

canonicalBehaviourOnlyBackwardAudit : FormationBackwardAudit
canonicalBehaviourOnlyBackwardAudit = formation-backward-audit
  recovered bounded unresolved unresolved unresolved unresolved
  nonidentifiableFromSurface nonidentifiableFromSurface nonidentifiableFromSurface

record ChildReligiousFormationBidi : Set where
  constructor child-religious-formation-bidi
  field
    paperSource : Brown.BrownPaperSource
    forwardEpisode : FormationEpisode
    backwardAudit : FormationBackwardAudit
    existingClaimAuditBoundary : ClaimAudit.ReligiousPowerBidiBoundary
    autonomyBoundary : Autonomy.AutonomyBoundary

open ChildReligiousFormationBidi public

canonicalChildReligiousFormationBidi : ChildReligiousFormationBidi
canonicalChildReligiousFormationBidi = child-religious-formation-bidi
  Brown.johnAnthonyBrownPaper
  closedFormationEpisode
  canonicalBehaviourOnlyBackwardAudit
  ClaimAudit.canonicalReligiousPowerBidiBoundary
  Autonomy.canonicalAutonomyBoundary

brownHellClaimStillNeedsMechanismReceipt : Brown.FormalObligation
brownHellClaimStillNeedsMechanismReceipt =
  Brown.paperToPrimaryObligation Brown.hellDamnationFearClaim

brownEarlyFormationStillNeedsCapacityReceipt : Brown.FormalObligation
brownEarlyFormationStillNeedsCapacityReceipt =
  Brown.paperToPrimaryObligation Brown.earlyGodSatanFormationClaim

record ChildReligiousAutonomyFormationBoundary : Set where
  constructor child-religious-autonomy-formation-boundary
  field
    autonomyIsMultidimensional : Bool
    samePublicActionDeterminesAutonomy : Bool
    earlyFormationAloneEqualsCoercion : Bool
    parentalGuidanceEqualsOwnershipOfBelief : Bool
    threatRepresentationEqualsExperiencedFear : Bool
    experiencedFearEqualsEntrapment : Bool
    outwardParticipationEqualsConsent : Bool
    religiousIdentityEqualsAutonomousEndorsement : Bool
    laterReopeningConditionsMatter : Bool
    observedConformityRecoversUniqueFormationRoute : Bool
    manuscriptHypothesisEqualsEstablishedEmpiricalFact : Bool

canonicalChildReligiousAutonomyFormationBoundary :
  ChildReligiousAutonomyFormationBoundary
canonicalChildReligiousAutonomyFormationBoundary =
  child-religious-autonomy-formation-boundary
    true false false false false false false false true false false
