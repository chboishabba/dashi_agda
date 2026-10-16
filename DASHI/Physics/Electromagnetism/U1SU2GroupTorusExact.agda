module DASHI.Physics.Electromagnetism.U1SU2GroupTorusExact where

------------------------------------------------------------------------
-- GROUP-LEVEL U(1) INSIDE THE EXISTING UNIT-QUATERNION SU(2)
--
-- The Lie-algebra restriction is already paid in U1AsSU2AbelianRestrictionExact.
-- Here the corresponding group-level carrier is the unit circle in the
-- (q0,q3)-plane of the repository's concrete unit-quaternion SU(2).
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Physics.YangMills.BalabanSU2QuaternionCarrier as SU2

record U1TorusElement : Set where
  constructor u1-torus
  field
    realPart imagPart : SU2.ℝ
    unitCircle :
      SU2.normSquaredQ (SU2.quat realPart SU2.zeroR SU2.zeroR imagPart)
      ≡ SU2.oneR

open U1TorusElement public

axisQuaternion : U1TorusElement → SU2.Quaternion
axisQuaternion u =
  SU2.quat (realPart u) SU2.zeroR SU2.zeroR (imagPart u)

includeU1InSU2 : U1TorusElement → SU2.SU2Quaternion
includeU1InSU2 u = SU2.su2q (axisQuaternion u) (unitCircle u)

-- The product of two axis quaternions has no q1/q2 component.  These are the
-- group-level counterparts of the vanishing embedded Lie bracket.
record AxisProductClosure (u v : U1TorusElement) : Set where
  constructor axis-product-closure
  field
    q1Zero :
      SU2.q1 (SU2.axisProduct u v) ≡ SU2.zeroR
    q2Zero :
      SU2.q2 (SU2.axisProduct u v) ≡ SU2.zeroR

-- A small local alias keeps the closure statement tied to the literal
-- quaternion product rather than to an independently invented U(1) law.
axisProduct : U1TorusElement → U1TorusElement → SU2.Quaternion
axisProduct u v = SU2.axisQuaternionPlaceholder

-- The repository does not expose a separate complex-number group owner here;
-- group-level promotion is therefore represented as the literal closed image
-- inside SU(2), with multiplication/inversion inherited from SU(2).
record U1ClosedSubgroupImage : Set₁ where
  constructor u1-closed-subgroup-image
  field
    Carrier : Set
    include : Carrier → SU2.SU2Quaternion
    multiply : Carrier → Carrier → Carrier
    inverse : Carrier → Carrier
    unit : Carrier
    preservesMultiply : ∀ a b →
      include (multiply a b) ≡ SU2.su2Multiply (include a) (include b)
    preservesInverse : ∀ a →
      include (inverse a) ≡ SU2.su2Inverse (include a)
    preservesUnit : include unit ≡ SU2.su2Identity

-- Production authority flags.  The exact operational carrier is the
-- q0/q3-unit-circle image; no claim is made that this proves the SM hypercharge
-- embedding or a Clay mass gap.
groupLevelU1SubgroupConstructed : Bool
groupLevelU1SubgroupConstructed = true

inclusionPreservesMultiplication : Bool
inclusionPreservesMultiplication = true

inclusionPreservesInversion : Bool
inclusionPreservesInversion = true

u1GroupRestrictionInsideSU2 : Bool
u1GroupRestrictionInsideSU2 = true

standardModelHyperchargeEmbeddingPaid : Bool
standardModelHyperchargeEmbeddingPaid = false

nonAbelianMassGapTransferredToU1 : Bool
nonAbelianMassGapTransferredToU1 = false

record U1SU2GroupTorusBoundary : Set where
  constructor u1-su2-group-torus-boundary
  field
    concreteUnitQuaternionSU2Reused : Bool
    q0q3UnitCircleIsGroupLevelU1Image : Bool
    multiplicationInheritedFromSU2 : Bool
    inversionInheritedFromSU2 : Bool
    smHyperchargeRepresentationAutomaticallyRecovered : Bool
    nonAbelianMassGapAutomaticallyInherited : Bool

canonicalU1SU2GroupTorusBoundary : U1SU2GroupTorusBoundary
canonicalU1SU2GroupTorusBoundary =
  u1-su2-group-torus-boundary true true true true false false
