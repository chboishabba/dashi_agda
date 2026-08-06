module DASHI.Mathematics.Topology.QuaternionS3PoincareCrossPollination where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Heinz Hopf,
-- "Über die Abbildungen der dreidimensionalen Sphäre auf die Kugelfläche".
-- DOI: 10.1007/BF01457962.
--
-- Richard S. Hamilton,
-- "Three-manifolds with positive Ricci curvature".
-- DOI: 10.4310/jdg/1214436922.
--
-- DASHI CONTRIBUTION
--
-- Connect the repository's proof-bearing unit-quaternion carrier to the round
-- S^3 Ricci-flow and Poincaré surfaces.  Unit quaternions are already closed
-- under multiplication by exact norm composition; the round-radius flow is
-- exact.  Identifying that algebraic carrier with the smooth three-sphere,
-- transporting the round metric, and proving the topological classification
-- are explicit bridge obligations.
------------------------------------------------------------------------

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Mathematics.Topology.QuaternionHopfUnitOrbitExact as Hopf
import DASHI.Mathematics.Topology.RoundThreeSphereRicciFlowExact as Round
import DASHI.Mathematics.Topology.PoincareGeometrizationExactBoundary as P

unitQuaternionProductReused :
  Hopf.UnitQuaternion → Hopf.UnitQuaternion → Hopf.UnitQuaternion
unitQuaternionProductReused = Hopf.unitQuaternionCompose

unitQuaternionIdentityReused : Hopf.UnitQuaternion
unitQuaternionIdentityReused = Hopf.unitQuaternionIdentity

record QuaternionSmoothThreeSphereBridge : Setω where
  field
    smoothContext : P.ThreeManifoldContext
    threeSphere : P.ThreeManifold smoothContext
    unitQuaternionToSphere : Hopf.UnitQuaternion → P.ThreeManifold smoothContext
    sphereToUnitQuaternion : P.ThreeManifold smoothContext → Hopf.UnitQuaternion
    carrierIdentification : Set
    multiplicationIsLieGroupLaw : Set
    smoothStructureCompatibility : Set
    roundMetricCompatibility : Set
    hopfCircleActionCompatibility : Set
    simplyConnectedProof : P.simplyConnected smoothContext threeSphere
    sphericalGeometryProof : P.sphericalGeometry smoothContext threeSphere

record QuaternionRicciPoincareBridge : Setω where
  field
    quaternionSphere : QuaternionSmoothThreeSphereBridge
    roundFlow : Round.RoundThreeSphereRicciFlow
    roundFlowLivesOnQuaternionSphere : Set
    arbitraryMetricComparison : Set
    ricciFlowToRoundOrSurgery : Set
    geometrizationInput : P.GeometrizationForSimplyConnected
      (QuaternionSmoothThreeSphereBridge.smoothContext quaternionSphere)
    sphericalClassification : P.SphericalSimplyConnectedClassification
      (QuaternionSmoothThreeSphereBridge.smoothContext quaternionSphere)

open QuaternionRicciPoincareBridge public

poincareConclusionFromQuaternionBridge :
  ∀ bridge →
  P.PoincareConclusion
    (QuaternionSmoothThreeSphereBridge.smoothContext
      (quaternionSphere bridge))
poincareConclusionFromQuaternionBridge bridge =
  P.geometrizationAndSphericalClassificationGivePoincare
    (QuaternionSmoothThreeSphereBridge.smoothContext
      (quaternionSphere bridge))
    (geometrizationInput bridge)
    (sphericalClassification bridge)

data ThreeSphereOwner : Set where
  unitQuaternionAlgebra
  smoothRoundThreeSphere
  arbitrarySimplyConnectedThreeManifold
  geometrizationClassification

unitQuaternionAlgebraIsNotGeometrization :
  unitQuaternionAlgebra ≡ geometrizationClassification → ⊥
unitQuaternionAlgebraIsNotGeometrization ()
