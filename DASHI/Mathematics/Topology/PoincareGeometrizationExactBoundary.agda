module DASHI.Mathematics.Topology.PoincareGeometrizationExactBoundary where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Richard S. Hamilton,
-- "Three-manifolds with positive Ricci curvature".
-- DOI: 10.4310/jdg/1214436922.
--
-- Grisha Perelman,
-- "The entropy formula for the Ricci flow and its geometric applications".
-- DOI: 10.48550/arXiv.math/0211159.
--
-- Grisha Perelman,
-- "Ricci flow with surgery on three-manifolds".
-- DOI: 10.48550/arXiv.math/0303109.
--
-- DASHI CONTRIBUTION
--
-- State the exact logical final step from geometrization to Poincaré: if every
-- closed connected simply connected three-manifold is spherical, and every
-- simply connected spherical three-manifold is homeomorphic to S^3, then the
-- Poincaré conclusion follows by composition.
--
-- The module reuses the existing Perelman fail-closed authority socket and the
-- exact round-sphere Ricci-flow calculation.  It does not supply smooth Ricci
-- flow with surgery, canonical neighborhoods, collapsing analysis or the
-- geometrization theorem itself.
------------------------------------------------------------------------

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Data.Rational.Base using (0ℚ; _*_)

import DASHI.Mathematics.Topology.RoundThreeSphereRicciFlowExact as Round
import DASHI.Physics.Closure.PerelmanRicciFlowAndGeometrizationBoundaryReceipt as Existing

record ThreeManifoldContext : Set₁ where
  field
    ThreeManifold : Set
    closed : ThreeManifold → Set
    connected : ThreeManifold → Set
    simplyConnected : ThreeManifold → Set
    sphericalGeometry : ThreeManifold → Set
    homeomorphicToS3 : ThreeManifold → Set

open ThreeManifoldContext public

record GeometrizationForSimplyConnected
    (context : ThreeManifoldContext) : Setω where
  field
    geometrize : ∀ manifold →
      closed context manifold →
      connected context manifold →
      simplyConnected context manifold →
      sphericalGeometry context manifold

open GeometrizationForSimplyConnected public

record SphericalSimplyConnectedClassification
    (context : ThreeManifoldContext) : Setω where
  field
    classifySpherical : ∀ manifold →
      sphericalGeometry context manifold →
      simplyConnected context manifold →
      homeomorphicToS3 context manifold

open SphericalSimplyConnectedClassification public

record PoincareConclusion
    (context : ThreeManifoldContext) : Setω where
  field
    poincare : ∀ manifold →
      closed context manifold →
      connected context manifold →
      simplyConnected context manifold →
      homeomorphicToS3 context manifold

open PoincareConclusion public

geometrizationAndSphericalClassificationGivePoincare :
  ∀ context →
  GeometrizationForSimplyConnected context →
  SphericalSimplyConnectedClassification context →
  PoincareConclusion context
geometrizationAndSphericalClassificationGivePoincare
    context geometrization sphericalClassification = record
  { poincare = λ manifold closedWitness connectedWitness simplyConnectedWitness →
      classifySpherical sphericalClassification manifold
        (geometrize geometrization manifold
          closedWitness connectedWitness simplyConnectedWitness)
        simplyConnectedWitness
  }

existingGeometrizationAuthorityRemainsClosed : Existing.AuthoritySocket
existingGeometrizationAuthorityRemainsClosed =
  Existing.mkClosedSocket Existing.thurstonGeometrization

existingGeometrizationAuthorityIsFalse :
  Existing.authorityAvailable existingGeometrizationAuthorityRemainsClosed
  ≡ false
existingGeometrizationAuthorityIsFalse = refl

roundSphereExactModelReused : ∀ extinctionTime →
  Round.roundRadiusSquared (Round.four * extinctionTime) extinctionTime
  ≡ 0ℚ
roundSphereExactModelReused = Round.roundExtinctionAtConfiguredTime

record RicciFlowToGeometrizationBridge : Set₁ where
  field
    generalRicciFlow : Round.GeneralRicciFlowObligations
    perelmanAnalysis : Round.PerelmanAnalyticObligations
    primeDecomposition : Set
    jsjDecomposition : Set
    surgeryCanonicalNeighborhoods : Set
    finiteExtinctionOrThickThinAnalysis : Set
    thurstonGeometrization : Set

data PoincareProofStage : Set where
  roundMetricExactSolution
  arbitraryMetricRicciFlow
  entropyAndNoncollapsing
  surgeryWithCanonicalNeighborhoods
  geometrizationStage
  sphericalSpaceFormClassification
  poincareConclusionStage

roundModelDoesNotProveGeometrization :
  roundMetricExactSolution ≡ geometrizationStage → ⊥
roundModelDoesNotProveGeometrization ()
