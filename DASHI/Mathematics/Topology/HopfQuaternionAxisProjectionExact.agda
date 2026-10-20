module DASHI.Mathematics.Topology.HopfQuaternionAxisProjectionExact where

-- Concrete SU(2) quaternion axis map underlying the complex Hopf bundle:
-- q |-> q k q^{-1}. The identified S2 and smooth atlas are separate.
-- The centralizer hypothesis is explicit until the quaternion-coordinate
-- computation for the selected torus has been discharged.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; trans; sym)
import DASHI.Physics.YangMills.BalabanSU2QuaternionCarrier as Q
import DASHI.Physics.Electromagnetism.U1SU2GroupTorusExact as U
import DASHI.Mathematics.Topology.HopfU1CosetOrbitExact as Orbit

axisQuaternion : Q.Quaternion
axisQuaternion = Q.quat Q.zeroR Q.zeroR Q.zeroR Q.oneR

axisMap : Orbit.Total → Q.Quaternion
axisMap g =
  Q._*q_ (Q._*q_ (Q.quaternion g) axisQuaternion)
    (Q.quaternion (Q.su2Inverse g))

-- An honest, named algebraic prerequisite: all phases commute with k.
-- This can be discharged by the repository's real polynomial solver.
record AxisCentralizer : Set where
  field
    commutes : (u : U.U1TorusElement) →
      Q._*q_ (Q.quaternion (U.includeU1InSU2 u)) axisQuaternion
      ≡ Q._*q_ axisQuaternion
          (Q.quaternion (U.includeU1InSU2 u))

-- Equivariance is stated at the SU2 group level, without identifying
-- spatial three-vectors until an S2 representation is provided.
record AxisFibreNaturality : Set where
  field
    phaseInvariant : (g : Orbit.Total) (u : U.U1TorusElement) →
      axisMap (Orbit.rightPhase g u) ≡ axisMap g
    fibreComplete : (g h : Orbit.Total) →
      axisMap g ≡ axisMap h → Orbit.SameOrbit g h

record GeometricHopfChartUpgrade : Set₁ where
  field
    axisCentralizer : AxisCentralizer
    axisNaturality : AxisFibreNaturality
    BaseSphere : Set
    northChart southChart : Set
    northChartWitness : northChart
    southChartWitness : southChart
    axisIdentifiesSphere : Set
    axisSphereWitness : axisIdentifiesSphere
    smoothLocalSections : Set
    smoothSectionsWitness : smoothLocalSections

-- No canonical inhabitant is asserted: centralizer, S2 equivalence,
-- free/transitive geometric fibres, and smooth charts are open.
