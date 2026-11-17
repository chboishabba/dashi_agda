module DASHI.Physics.ExoticGravity.AntigravityNegativeGCouplingScopeProofSearchExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)

import DASHI.Physics.ExoticGravity.AntigravityNegativeGCouplingScopeBidiExact as Scope
import DASHI.Physics.ExoticGravity.AntigravityMaterialBidiCrossPollinationExact as Material
import DASHI.Physics.ExoticGravity.AntigravityNegativeGCrossScaleProofSearchExact as Universal
import DASHI.Law.SensibLawProofDirectedSearchIntentExact as Search

------------------------------------------------------------------------
-- COUPLING-SCOPE-INDEXED PROOF SEARCH
--
-- Same local repulsive surface, different scope -> different highest-alpha
-- experiment.  This is a thin scheduler over existing owners, not a new planner.
------------------------------------------------------------------------

data ScopeSearchStage : Set where
  universalLocalSignDiscriminator : ScopeSearchStage
  universalCrossScaleConsistency : ScopeSearchStage
  materialSameApparatusRegimeContrast : ScopeSearchStage
  materialOrdinaryRegimeNegativeControl : ScopeSearchStage
  materialIndependentRegimeReplication : ScopeSearchStage
  sourceCarrierIdentityLock : ScopeSearchStage
  sourceSpecificReplication : ScopeSearchStage
  scopeContradictionAssessment : ScopeSearchStage

firstStageForScope : Scope.CouplingScope → ScopeSearchStage
firstStageForScope Scope.universalNewtonCoupling = universalLocalSignDiscriminator
firstStageForScope Scope.materialEffectiveCoupling = materialSameApparatusRegimeContrast
firstStageForScope Scope.sourceSpecificEffectiveCoupling = sourceCarrierIdentityLock

producerForScopeStage : ScopeSearchStage → Search.ProducerClass
producerForScopeStage universalLocalSignDiscriminator = Search.empiricalEvidenceProducer
producerForScopeStage universalCrossScaleConsistency = Search.identityProducer
producerForScopeStage materialSameApparatusRegimeContrast = Search.discriminatorProducer
producerForScopeStage materialOrdinaryRegimeNegativeControl = Search.empiricalEvidenceProducer
producerForScopeStage materialIndependentRegimeReplication = Search.empiricalEvidenceProducer
producerForScopeStage sourceCarrierIdentityLock = Search.identityProducer
producerForScopeStage sourceSpecificReplication = Search.empiricalEvidenceProducer
producerForScopeStage scopeContradictionAssessment = Search.contradictionProducer

------------------------------------------------------------------------
-- Material-effective route: the sign hypothesis must track the regime on the
-- same apparatus rather than silently changing the universal Newton constant.
------------------------------------------------------------------------

record MaterialEffectiveGExperimentTarget : Set where
  constructor material-effective-g-experiment-target
  field
    sameApparatusAcrossRegimes : Bool
    ordinaryRegime : Material.AntigravityMaterialRegime
    candidateRegime : Material.AntigravityMaterialRegime
    ordinaryRegimeIsOrdinary : ordinaryRegime ≡ Material.ordinaryRegime
    candidateRegimeIsNonOrdinary : candidateRegime ≡ Material.ordinaryRegime → ⊥
    sameConsumerDiscriminator : Bool
    sameCalibrationFamily : Bool
    transitionStateMeasured : Bool
    ordinaryBackgroundsClosedInBothRegimes : Bool
    independentReplicationRequired : Bool

open MaterialEffectiveGExperimentTarget public

coherentMaterialEffectiveGTarget : MaterialEffectiveGExperimentTarget
coherentMaterialEffectiveGTarget =
  material-effective-g-experiment-target
    true
    Material.ordinaryRegime
    Material.coherentRegime
    refl
    (λ ())
    true true true true true

------------------------------------------------------------------------
-- Exact introspective collision: observing only a local repulsive surface does
-- not tell the scheduler whether to search cross-scale universality or a
-- same-apparatus material transition.
------------------------------------------------------------------------

data SearchFixture : Set where
  universalScopeFixture materialScopeFixture : SearchFixture

data CoarseAnomalySurface : Set where
  sameLocalRepulsiveSurface : CoarseAnomalySurface

coarseObserve : SearchFixture → CoarseAnomalySurface
coarseObserve _ = sameLocalRepulsiveSurface

fixtureScope : SearchFixture → Scope.CouplingScope
fixtureScope universalScopeFixture = Scope.universalNewtonCoupling
fixtureScope materialScopeFixture = Scope.materialEffectiveCoupling

searchStage : SearchFixture → ScopeSearchStage
searchStage fixture = firstStageForScope (fixtureScope fixture)

coarseCollision :
  coarseObserve universalScopeFixture ≡ coarseObserve materialScopeFixture
coarseCollision = refl

coarseAnomalyDoesNotDetermineSearchStage :
  searchStage universalScopeFixture ≡ searchStage materialScopeFixture → ⊥
coarseAnomalyDoesNotDetermineSearchStage ()

record NegativeGCouplingScopeProofSearchBoundary : Set where
  constructor negative-g-coupling-scope-proof-search-boundary
  field
    universalAndMaterialScopesHaveSameFirstSearchStage : Bool
    universalScopeStartsWithLocalSignDiscriminator : Bool
    materialScopeStartsWithSameApparatusRegimeContrast : Bool
    materialRouteRequiresOrdinaryRegimeNegativeControl : Bool
    materialRouteRequiresIndependentReplication : Bool
    materialRouteAutomaticallyMutatesUniversalNewtonG : Bool
    scopeSelectionRequiresEvidenceBeyondLocalRepulsiveSurface : Bool

canonicalNegativeGCouplingScopeProofSearchBoundary :
  NegativeGCouplingScopeProofSearchBoundary
canonicalNegativeGCouplingScopeProofSearchBoundary =
  negative-g-coupling-scope-proof-search-boundary
    false true true true true false true

existingUniversalSearchBoundary : Universal.NegativeGCrossScaleProofSearchBoundary
existingUniversalSearchBoundary = Universal.canonicalNegativeGCrossScaleProofSearchBoundary
