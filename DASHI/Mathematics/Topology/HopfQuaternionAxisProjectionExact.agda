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
open import Data.List.Base using ([]; _∷_)
open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)
import Tactic.RingSolver as Solver
import DASHI.Physics.YangMills.QuaternionConjugationProductExact as Conj

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

-- Polynomial centralizer: the selected complex plane (q0,q3)
-- commutes with its unit imaginary basis k, without imposing an
-- arbitrary new axiom or identifying all SU2 rotations as abelian.
axisCentralizerPolynomial :
  (a b : ℝ) →
  Q._*q_ (Q.quat a Q.zeroR Q.zeroR b) axisQuaternion ≡
  Q._*q_ axisQuaternion (Q.quat a Q.zeroR Q.zeroR b)
axisCentralizerPolynomial a b =
  Q.quaternionExt
    (Solver.solve (a ∷ b ∷ []) Q.realSolverRing)
    (Solver.solve (a ∷ b ∷ []) Q.realSolverRing)
    (Solver.solve (a ∷ b ∷ []) Q.realSolverRing)
    (Solver.solve (a ∷ b ∷ []) Q.realSolverRing)

canonicalAxisCentralizer : AxisCentralizer
canonicalAxisCentralizer = record
  { commutes = λ u →
      axisCentralizerPolynomial (U.realPart u) (U.imagPart u)
  }

-- Centralizer + unit inverse imply phase conjugation fixes k.
phaseFixesAxis : (u : U.U1TorusElement) →
  Q._*q_
    (Q._*q_ (Q.quaternion (U.includeU1InSU2 u)) axisQuaternion)
    (Q.conjugateQ (Q.quaternion (U.includeU1InSU2 u)))
  ≡ axisQuaternion
phaseFixesAxis u =
  let p = U.includeU1InSU2 u
      x = Q.quaternion p
  in
  trans
    (cong (λ y → Q._*q_ y (Q.conjugateQ x))
      (AxisCentralizer.commutes canonicalAxisCentralizer u))
    (trans
      (Q.quaternionMultiplyAssociative axisQuaternion x (Q.conjugateQ x))
      (trans
        (cong (Q._*q_ axisQuaternion)
          (cong Q.quaternion (Q.su2InverseRight p)))
        (Q.quaternionOneRight axisQuaternion)))

-- The next geometric fact is now a consequence of concrete
-- multiplication, the shared YM conjugation anti-homomorphism, and
-- the circle centralizer; no atlas/smoothness assumption is involved.
canonicalAxisPhaseInvariant :
  (g : Orbit.Total) (u : U.U1TorusElement) →
  axisMap (Orbit.rightPhase g u) ≡ axisMap g
canonicalAxisPhaseInvariant g u =
  let x = Q.quaternion g
      y = Q.quaternion (U.includeU1InSU2 u)
      cy = Q.conjugateQ y
      cx = Q.conjugateQ x
  in
  trans
    (cong (λ z → Q._*q_ (Q._*q_ (Q._*q_ x y) axisQuaternion) z)
      (Conj.conjugateProduct x y))
    (trans
      (sym (Q.quaternionMultiplyAssociative
        (Q._*q_ (Q._*q_ x y) axisQuaternion) cy cx))
      (trans
        (cong (λ z → Q._*q_ (Q._*q_ z cy) cx)
          (Q.quaternionMultiplyAssociative x y axisQuaternion))
        (trans
          (cong (λ z → Q._*q_ z cx)
            (Q.quaternionMultiplyAssociative x
              (Q._*q_ y axisQuaternion) cy))
          (cong (λ z → Q._*q_ (Q._*q_ x z) cx)
            (phaseFixesAxis u)))))

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
