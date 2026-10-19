module DASHI.Mathematics.Topology.HopfU1CosetOrbitExact where

-- Concrete homogeneous-space precursor to S1 -> S3 -> S2.
-- Total = the existing SU(2) group (unit quaternions).
-- The quotient is represented by the orbit relation, NOT falsely
-- identified with a smooth S2 or a quotient type without proof.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)
open import DASHI.Core.Prelude
import DASHI.Physics.Electromagnetism.U1SU2GroupTorusExact as U1
import DASHI.Physics.YangMills.BalabanSU2QuaternionCarrier as SU2

Total : Set
Total = SU2.SU2Quaternion

Phase : Set
Phase = U1.U1TorusElement

phase : Phase → Total
phase = U1.includeU1InSU2

rightPhase : Total → Phase → Total
rightPhase g u = SU2.su2Multiply g (phase u)

rightUnit : (g : Total) → rightPhase g U1.u1Identity ≡ g
rightUnit g =
  trans (cong (SU2.su2Multiply g) U1.includePreservesIdentity)
        (SU2.su2IdentityRight g)

rightComposition : (g : Total) (u v : Phase) →
  rightPhase (rightPhase g u) v
  ≡ rightPhase g (U1.u1Multiply u v)
rightComposition g u v =
  trans (SU2.su2MultiplyAssociative g (phase u) (phase v))
    (sym (cong (SU2.su2Multiply g) (U1.includePreservesMultiply u v)))

-- This does not require injectivity of the inclusion.
-- It does require the ordinary group inverse laws already proved for SU(2).
rightPhaseFixesOnlyIdentityImage :
  (g : Total) (u : Phase) →
  rightPhase g u ≡ g →
  phase u ≡ SU2.su2Identity
rightPhaseFixesOnlyIdentityImage g u eq =
  trans
    (sym (SU2.su2IdentityLeft (phase u)))
    (trans
      (sym (cong (λ x → SU2.su2Multiply x (phase u))
        (SU2.su2InverseLeft g)))
      (trans
        (SU2.su2MultiplyAssociative
          (SU2.su2Inverse g) g (phase u))
        (trans
          (cong (SU2.su2Multiply (SU2.su2Inverse g)) eq)
          (SU2.su2InverseLeft g))))

-- Orbit equivalence, formulated with a concrete witness rather than
-- an assumed pre-existing smooth quotient.
record SameOrbit (g h : Total) : Set where
  constructor sameOrbit
  field
    witness : Phase
    relates : rightPhase g witness ≡ h
open SameOrbit public

orbitReflexive : (g : Total) → SameOrbit g g
orbitReflexive g = sameOrbit U1.u1Identity (rightUnit g)

orbitSymmetric : (g h : Total) → SameOrbit g h → SameOrbit h g
orbitSymmetric g h (sameOrbit u proof) =
  sameOrbit (U1.u1Inverse u)
    (trans
      (sym (cong (λ x → rightPhase x (U1.u1Inverse u)) proof))
      (trans
        (rightComposition g u (U1.u1Inverse u))
        (trans
          (cong (rightPhase g) (U1.u1InverseRight u))
          (rightUnit g))))

orbitTransitive : (g h k : Total) →
  SameOrbit g h → SameOrbit h k → SameOrbit g k
orbitTransitive g h k (sameOrbit u p) (sameOrbit v q) =
  sameOrbit (U1.u1Multiply u v)
    (trans
      (sym (rightComposition g u v))
      (trans
        (cong (λ x → rightPhase x v) p)
        q))

-- The true smooth Hopf fibration requires identifying these cosets
-- with S2 and building smooth local trivialisations. Neither follows
-- from the orbit equivalence theorem alone.
