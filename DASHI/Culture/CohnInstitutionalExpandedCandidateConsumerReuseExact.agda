module DASHI.Culture.CohnInstitutionalExpandedCandidateConsumerReuseExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

import DASHI.Core.BenefitBurdenExternalityDistributionExact as Distribution
import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Core.InstitutionalNormProductionExact as Norm
import DASHI.Core.InstitutionalProximityInfluenceAdequacyExact as Proximity
import DASHI.Core.RepresentationSubjectPositionNonfactorabilityExact as Subject
import DASHI.Cognition.PNF.SensibLawDominantChartEpistemicCompressionCrossPollinationExact as Dominant
import DASHI.Culture.CohnInstitutionalEpistemicActivismConsumer369Exact as Activism
import DASHI.Culture.CohnInstitutionalExpandedCandidateFibreAskExact as Ask
import DASHI.Governance.FirstNationsOwnedEvidenceContractExact as FirstNations
import DASHI.Governance.MoretonRobinsonRecognitionSovereigntyBoundaryExact as Sovereignty
import DASHI.Governance.SituatedDissentDeceptionAssayExact as Dissent

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
  existingNeighbourConsumer
  existingNeighbourConsumer
  existingNeighbourConsumer
  existingNeighbourConsumer
  exactCanonicalOwner
  existingNeighbourConsumer
  existingNeighbourConsumer
  existingNeighbourConsumer
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

structuralExclusionNeighbour :
  INF.FactorsThrough INF.flatProjection INF.relationalOutcome → ⊥
structuralExclusionNeighbour = Dominant.singleAxisCannotCarrySituatedRelationalOutcome

researchBurdenNeighbour :
  INF.FactorsThrough Distribution.demoAggregate Distribution.demoBurden → ⊥
researchBurdenNeighbour = Distribution.aggregateCannotRecoverBurden

researchVoiceNeighbour :
  INF.FactorsThrough Distribution.demoAggregate Distribution.demoVoice → ⊥
researchVoiceNeighbour = Distribution.aggregateCannotRecoverVoice

consultationDoesNotPayBalancedParticipation :
  Norm.consultationAutomaticallyBalancedParticipation
    Norm.canonicalInstitutionalNormProductionBoundary ≡ false
consultationDoesNotPayBalancedParticipation = refl

accessDoesNotPayInfluence :
  Proximity.proximityAutomaticallyInfluence
    Proximity.canonicalInstitutionalProximityBoundary ≡ false
accessDoesNotPayInfluence = refl

------------------------------------------------------------------------
-- Exact application/canonical owners.
------------------------------------------------------------------------

activismConsumerBoundary : Activism.EpistemicActivismConsumerBoundary
activismConsumerBoundary = Activism.canonicalEpistemicActivismConsumerBoundary

activismNextProbeNonfactorability :
  INF.FactorsThrough Dissent.recordedDissent Activism.nextUptakeProbe → ⊥
activismNextProbeNonfactorability = Activism.recordedDissentCannotDetermineNextProbe

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
    genericBurdenGeometryEqualsEpistemicLabour : Bool
    genericBurdenGeometryEqualsIndigenousRelationalEthics : Bool
    reuseCanNarrowNextAcquisitionSearch : Bool

open ExpandedConsumerReuseBoundary public

canonicalExpandedConsumerReuseBoundary : ExpandedConsumerReuseBoundary
canonicalExpandedConsumerReuseBoundary = expanded-consumer-reuse-boundary
  false false false false false false false true

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
  "governance/permission -> FirstNationsOwnedEvidenceContractExact; recognition/sovereignty -> MoretonRobinsonRecognitionSovereigntyBoundaryExact; epistemic activism/proper uptake -> CohnInstitutionalEpistemicActivismConsumer369Exact"
  "structural epistemic exclusion -> dominant-chart/intersectional compression; epistemic labour + relational research burden -> BenefitBurdenExternalityDistributionExact research burden/voice geometry; participation power -> InstitutionalProximityInfluenceAdequacyExact; internal exclusion -> InstitutionalNormProductionExact; outsider-within standpoint -> RepresentationSubjectPositionNonfactorabilityExact; Two-Eyed coexistence/co-learning -> existing Indigenous knowledge/braiding owners"
  "none of the acquired source families lacks at least one theorem-bearing structural consumer; source-specific empirical instantiations remain unpaid where not separately observed"
  "the Ibrahim acquisition frontier is structurally saturated for the declared candidate families without identifying source concepts with the reused DASHI consumers"
  "shift from horizontal acquisition to concrete source-specific observation only when a real institutional case supplies the missing premise; otherwise reconcile/certify the branch"
