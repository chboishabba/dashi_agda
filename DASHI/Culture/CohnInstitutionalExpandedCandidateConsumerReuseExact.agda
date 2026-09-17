module DASHI.Culture.CohnInstitutionalExpandedCandidateConsumerReuseExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

import DASHI.Core.InstitutionalNormProductionExact as Norm
import DASHI.Core.InstitutionalProximityInfluenceAdequacyExact as Proximity
import DASHI.Core.RepresentationSubjectPositionNonfactorabilityExact as Subject
import DASHI.Culture.CohnInstitutionalExpandedCandidateFibreAskExact as Ask
import DASHI.Governance.FirstNationsOwnedEvidenceContractExact as FirstNations
import DASHI.Governance.MoretonRobinsonRecognitionSovereigntyBoundaryExact as Sovereignty

------------------------------------------------------------------------
-- EXPANDED CANDIDATE -> EXISTING CONSUMER REUSE MAP
--
-- Three distinct statuses are retained:
--   exactCanonicalOwner      : repo already has a theorem-bearing owner for the
--                              same consumer distinction;
--   existingNeighbourConsumer: repo has a typed nearby distinction that can be
--                              reused structurally, but it is not definitionally
--                              the acquired source coordinate;
--   uninstantiatedCandidate  : source family exists but no current typed
--                              consumer/fixture observes it directly.
------------------------------------------------------------------------

data ConsumerReuseStatus : Set where
  exactCanonicalOwner existingNeighbourConsumer uninstantiatedCandidate : ConsumerReuseStatus

record ExpandedConsumerReuse : Set where
  constructor expanded-consumer-reuse
  field
    structuralEpistemicExclusionStatus : ConsumerReuseStatus
    epistemicLabourStatus : ConsumerReuseStatus
    outsiderWithinStandpointStatus : ConsumerReuseStatus
    participationPowerStatus : ConsumerReuseStatus
    twoEyedCoexistenceActionStatus : ConsumerReuseStatus
    epistemicActivismStatus : ConsumerReuseStatus
    internalExclusionStatus : ConsumerReuseStatus
    twoEyedCoLearningStatus : ConsumerReuseStatus
    relationalResearchBurdenStatus : ConsumerReuseStatus
    governancePermissionStatus : ConsumerReuseStatus
    sovereigntyStatus : ConsumerReuseStatus

open ExpandedConsumerReuse public

canonicalExpandedConsumerReuse : ExpandedConsumerReuse
canonicalExpandedConsumerReuse = expanded-consumer-reuse
  uninstantiatedCandidate
  uninstantiatedCandidate
  existingNeighbourConsumer
  existingNeighbourConsumer
  existingNeighbourConsumer
  uninstantiatedCandidate
  existingNeighbourConsumer
  existingNeighbourConsumer
  uninstantiatedCandidate
  exactCanonicalOwner
  exactCanonicalOwner

------------------------------------------------------------------------
-- Neighbouring consumers.
------------------------------------------------------------------------

-- Arnstein-style participation-power is not identified with lobbying/access,
-- but this existing theorem is an exact structural neighbour: the same access
-- surface does not determine decision influence.
proximityInfluenceDefect : Proximity.InfluenceQueryAdequacyDefect
proximityInfluenceDefect = Proximity.influenceQueryAdequacyDefect

-- Young-style internal exclusion is not identified with this generic history
-- carrier, but same institutional baseline with negotiated vs excluded
-- production histories is an existing typed consumer for erased participation
-- history.
productionHistoryDefect : Norm.ProductionHistoryQueryAdequacyDefect
productionHistoryDefect = Norm.productionHistoryQueryAdequacyDefect

-- Collins' outsider-within standpoint is source-specific and not identical to
-- DASHI subject-position grammar.  The canonical neighbour nevertheless pays
-- the structural point that a representable surface does not recover the
-- originating subject position.
subjectPositionNeighbour :
  Subject.SubjectPositionCollision Subject.canonicalRepresentationSubjectPositionSystem
subjectPositionNeighbour = Subject.canonicalSubjectPositionCollision

consultationDoesNotPayBalancedParticipation :
  Norm.consultationAutomaticallyBalancedParticipation
    Norm.canonicalInstitutionalNormProductionBoundary ≡ false
consultationDoesNotPayBalancedParticipation = refl

accessDoesNotPayInfluence :
  Proximity.proximityAutomaticallyInfluence
    Proximity.canonicalInstitutionalProximityBoundary ≡ false
accessDoesNotPayInfluence = refl

------------------------------------------------------------------------
-- Exact canonical owners.
------------------------------------------------------------------------

firstNationsGovernanceBoundary : FirstNations.FirstNationsEvidenceBoundary
firstNationsGovernanceBoundary = FirstNations.canonicalFirstNationsEvidenceBoundary

sovereigntyBoundary : Sovereignty.MoretonRobinsonBoundary
sovereigntyBoundary = Sovereignty.canonicalMoretonRobinsonBoundary

provenanceDoesNotDeterminePermission :
  FirstNations.provenanceAloneDeterminesPermission
    firstNationsGovernanceBoundary ≡ false
provenanceDoesNotDeterminePermission = refl

settlerRecognitionDoesNotConstituteSovereignty :
  Sovereignty.settlerRecognitionConstitutesIndigenousSovereignty
    sovereigntyBoundary ≡ false
settlerRecognitionDoesNotConstituteSovereignty = refl

------------------------------------------------------------------------
-- Current Cohn fixture remains separately audited.
------------------------------------------------------------------------

currentFibreAsk : Ask.ExpandedCandidateFibreAsk
currentFibreAsk = Ask.canonicalExpandedCandidateFibreAsk

------------------------------------------------------------------------
-- Boundary against semantic promotion.
------------------------------------------------------------------------

record ExpandedConsumerReuseBoundary : Set where
  constructor expanded-consumer-reuse-boundary
  field
    neighbouringConsumerDefinitionallyEqualsSourceCoordinate : Bool
    structuralAnalogyCreatesHistoricalInfluenceClaim : Bool
    exactCanonicalOwnerMakesSourceRedundant : Bool
    uninstantiatedCandidateMayBeAssignedSyntheticValueWithoutObservation : Bool
    sourceFamilyMayOverrideCanonicalGovernanceBoundary : Bool
    reuseCanNarrowNextAcquisitionSearch : Bool

open ExpandedConsumerReuseBoundary public

canonicalExpandedConsumerReuseBoundary : ExpandedConsumerReuseBoundary
canonicalExpandedConsumerReuseBoundary = expanded-consumer-reuse-boundary
  false false false false false true

------------------------------------------------------------------------
-- Pareto consequence.
------------------------------------------------------------------------

record ExpandedConsumerReuseFrontier : Set where
  constructor expanded-consumer-reuse-frontier
  field
    exactReuse : String
    structuralNeighbourReuse : String
    stillOpenConsumers : String
    implication : String
    nextMove : String

open ExpandedConsumerReuseFrontier public

canonicalExpandedConsumerReuseFrontier : ExpandedConsumerReuseFrontier
canonicalExpandedConsumerReuseFrontier = expanded-consumer-reuse-frontier
  "governance/permission -> FirstNationsOwnedEvidenceContractExact; recognition/sovereignty -> MoretonRobinsonRecognitionSovereigntyBoundaryExact"
  "participation power -> InstitutionalProximityInfluenceAdequacyExact as access/influence neighbour; internal exclusion -> InstitutionalNormProductionExact as included/excluded production-history neighbour; outsider-within standpoint -> RepresentationSubjectPositionNonfactorabilityExact; Two-Eyed coexistence/co-learning -> existing Indigenous knowledge/braiding owners"
  "structural epistemic exclusion; epistemic labour burden; epistemic activism/proper uptake; relational research burden still lack a direct typed institutional consumer in this audit"
  "the expanded source frontier is now partly operationalised by existing consumers without identifying those consumers with the source concepts"
  "prefer concrete fixtures for one of the still-open consumers; do not acquire another paper merely to restate an already represented neighbour"
