module DASHI.Culture.CohnInstitutionalExpandedCandidateConsumerReuseExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Core.InstitutionalNormProductionExact as Norm
import DASHI.Core.InstitutionalProximityInfluenceAdequacyExact as Proximity
import DASHI.Core.RepresentationSubjectPositionNonfactorabilityExact as Subject
import DASHI.Cognition.PNF.SensibLawDominantChartEpistemicCompressionCrossPollinationExact as Dominant
import DASHI.Culture.CohnInstitutionalExpandedCandidateFibreAskExact as Ask
import DASHI.Governance.FirstNationsOwnedEvidenceContractExact as FirstNations
import DASHI.Governance.MoretonRobinsonRecognitionSovereigntyBoundaryExact as Sovereignty

------------------------------------------------------------------------
-- EXPANDED CANDIDATE -> EXISTING CONSUMER REUSE MAP
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
  existingNeighbourConsumer
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

proximityInfluenceDefect : Proximity.InfluenceQueryAdequacyDefect
proximityInfluenceDefect = Proximity.influenceQueryAdequacyDefect

productionHistoryDefect : Norm.ProductionHistoryQueryAdequacyDefect
productionHistoryDefect = Norm.productionHistoryQueryAdequacyDefect

subjectPositionNeighbour :
  INF.FactorsThrough Subject.categoryVisibility Subject.subjectPosition → ⊥
subjectPositionNeighbour = Subject.categoryVisibilityCannotRecoverSubjectPosition

-- Dotson's structural epistemic oppression is not identified with the DASHI
-- dominant-chart compiler.  This theorem is a structural neighbour: a single
-- axis/category observer cannot carry the situated relational-power outcome.
structuralExclusionNeighbour :
  INF.FactorsThrough INF.flatProjection INF.relationalOutcome → ⊥
structuralExclusionNeighbour = Dominant.singleAxisCannotCarrySituatedRelationalOutcome

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
  "structural epistemic exclusion -> dominant-chart/intersectional compression neighbour; participation power -> InstitutionalProximityInfluenceAdequacyExact; internal exclusion -> InstitutionalNormProductionExact; outsider-within standpoint -> RepresentationSubjectPositionNonfactorabilityExact; Two-Eyed coexistence/co-learning -> existing Indigenous knowledge/braiding owners"
  "epistemic labour burden; epistemic activism/proper uptake; relational research burden still lack a direct typed institutional consumer in this audit"
  "the expanded source frontier is now mostly operationalised by canonical or neighbouring consumers without identifying those consumers with the source concepts"
  "prefer concrete fixtures for one of the three still-open consumers; do not acquire another paper merely to restate an already represented neighbour"
