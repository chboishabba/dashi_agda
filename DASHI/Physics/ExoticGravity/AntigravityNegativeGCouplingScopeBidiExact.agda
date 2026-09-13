module DASHI.Physics.ExoticGravity.AntigravityNegativeGCouplingScopeBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Physics.GR.SignedEinsteinCouplingBidiExact as Signed
import DASHI.Physics.GR.UniversalSignedGCrossScaleFingerprintBidiExact as Universal
import DASHI.Physics.ExoticGravity.AntigravityMaterialBidiCrossPollinationExact as Material
import DASHI.Law.SensibLawProofDirectedSearchIntentExact as Search

------------------------------------------------------------------------
-- COUPLING SCOPE BIDI
--
-- A local/material effective coupling sign is a different hypothesis from a
-- universal sign change of Newton's gravitational constant.  The same local
-- repulsive observation can be compatible with multiple coupling scopes.
------------------------------------------------------------------------

data CouplingScope : Set where
  universalNewtonCoupling : CouplingScope
  materialEffectiveCoupling : CouplingScope
  sourceSpecificEffectiveCoupling : CouplingScope

data ScopeObligation : Set where
  crossScaleUniversalConsistency : ScopeObligation
  materialRegimeSpecificConsistency : ScopeObligation
  sourceCarrierSpecificConsistency : ScopeObligation

scopeObligation : CouplingScope → ScopeObligation
scopeObligation universalNewtonCoupling = crossScaleUniversalConsistency
scopeObligation materialEffectiveCoupling = materialRegimeSpecificConsistency
scopeObligation sourceSpecificEffectiveCoupling = sourceCarrierSpecificConsistency

record ScopedSignedCouplingHypothesis : Set where
  constructor scoped-signed-coupling-hypothesis
  field
    couplingSign : Signed.CouplingSign
    couplingScope : CouplingScope
    materialRegime : Material.AntigravityMaterialRegime
    sourceCarrier : String
    scopeClaim : String

open ScopedSignedCouplingHypothesis public

universalNegativeGHypothesis : ScopedSignedCouplingHypothesis
universalNegativeGHypothesis =
  scoped-signed-coupling-hypothesis
    Signed.negativeCoupling
    universalNewtonCoupling
    Material.ordinaryRegime
    "universal gravitational coupling"
    "counterfactual universal sign flip of the gravitational coupling"

coherentMaterialNegativeEffectiveGHypothesis : ScopedSignedCouplingHypothesis
coherentMaterialNegativeEffectiveGHypothesis =
  scoped-signed-coupling-hypothesis
    Signed.negativeCoupling
    materialEffectiveCoupling
    Material.coherentRegime
    "coherent engineered material/source"
    "counterfactual negative effective gravitational coupling restricted to a coherent material regime"

------------------------------------------------------------------------
-- Exact local-observation collision.
------------------------------------------------------------------------

data LocalRepulsiveFixture : Set where
  universalNegativeGFixture : LocalRepulsiveFixture
  coherentEffectiveNegativeGFixture : LocalRepulsiveFixture

data CoarseLocalRepulsiveObservation : Set where
  localRepulsiveGravityLikeResponse : CoarseLocalRepulsiveObservation

coarseLocalObservation : LocalRepulsiveFixture → CoarseLocalRepulsiveObservation
coarseLocalObservation _ = localRepulsiveGravityLikeResponse

fixtureScope : LocalRepulsiveFixture → CouplingScope
fixtureScope universalNegativeGFixture = universalNewtonCoupling
fixtureScope coherentEffectiveNegativeGFixture = materialEffectiveCoupling

localScopeCollision :
  coarseLocalObservation universalNegativeGFixture
    ≡ coarseLocalObservation coherentEffectiveNegativeGFixture
localScopeCollision = refl

localRepulsionDoesNotDetermineCouplingScope :
  fixtureScope universalNegativeGFixture
    ≡ fixtureScope coherentEffectiveNegativeGFixture → ⊥
localRepulsionDoesNotDetermineCouplingScope ()

record RefinedCouplingScopeObserver : Set where
  constructor refined-coupling-scope-observer
  field
    localResponse : CoarseLocalRepulsiveObservation
    scope : CouplingScope
    regime : Material.AntigravityMaterialRegime

refinedScopeObserve : LocalRepulsiveFixture → RefinedCouplingScopeObserver
refinedScopeObserve universalNegativeGFixture =
  refined-coupling-scope-observer
    localRepulsiveGravityLikeResponse
    universalNewtonCoupling
    Material.ordinaryRegime
refinedScopeObserve coherentEffectiveNegativeGFixture =
  refined-coupling-scope-observer
    localRepulsiveGravityLikeResponse
    materialEffectiveCoupling
    Material.coherentRegime

refinedScopeFixturesDistinct :
  refinedScopeObserve universalNegativeGFixture
    ≡ refinedScopeObserve coherentEffectiveNegativeGFixture → ⊥
refinedScopeFixturesDistinct ()

------------------------------------------------------------------------
-- Reverse proof-search obligations differ by scope.
------------------------------------------------------------------------

data CouplingScopeResidual : Set where
  missingScopeIdentity : CouplingScopeResidual
  missingMaterialRegimeIdentity : CouplingScopeResidual
  missingSourceCarrierIdentity : CouplingScopeResidual
  missingUniversalCrossScaleFingerprint : CouplingScopeResidual
  missingMaterialRegimeReplication : CouplingScopeResidual
  missingOrdinaryRegimeNegativeControl : CouplingScopeResidual
  scopeContradictionOpen : CouplingScopeResidual

producerForCouplingScopeResidual : CouplingScopeResidual → Search.ProducerClass
producerForCouplingScopeResidual missingScopeIdentity = Search.identityProducer
producerForCouplingScopeResidual missingMaterialRegimeIdentity = Search.identityProducer
producerForCouplingScopeResidual missingSourceCarrierIdentity = Search.identityProducer
producerForCouplingScopeResidual missingUniversalCrossScaleFingerprint = Search.propositionSourceProducer
producerForCouplingScopeResidual missingMaterialRegimeReplication = Search.empiricalEvidenceProducer
producerForCouplingScopeResidual missingOrdinaryRegimeNegativeControl = Search.empiricalEvidenceProducer
producerForCouplingScopeResidual scopeContradictionOpen = Search.contradictionProducer

existingUniversalBoundary : Universal.UniversalSignedGCrossScaleBoundary
existingUniversalBoundary = Universal.canonicalUniversalSignedGCrossScaleBoundary

record NegativeGCouplingScopeBoundary : Set where
  constructor negative-g-coupling-scope-boundary
  field
    localNegativeEffectiveCouplingEqualsUniversalNegativeG : Bool
    materialRegimeChangeAutomaticallyChangesUniversalNewtonG : Bool
    localRepulsiveObservationDeterminesCouplingScope : Bool
    universalNegativeGRequiresCrossScaleConsistency : Bool
    materialEffectiveNegativeGRequiresRegimeSpecificReplication : Bool
    materialEffectiveNegativeGRequiresOrdinaryRegimeNegativeControl : Bool
    rejectionOfUniversalNegativeGRejectsMaterialEffectiveNegativeG : Bool
    materialEffectiveNegativeGAutomaticallyProvesAmyOrLiTorrMechanism : Bool

canonicalNegativeGCouplingScopeBoundary : NegativeGCouplingScopeBoundary
canonicalNegativeGCouplingScopeBoundary =
  negative-g-coupling-scope-boundary
    false false false true true true false false
