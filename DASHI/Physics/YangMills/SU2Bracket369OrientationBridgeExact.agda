module DASHI.Physics.YangMills.SU2Bracket369OrientationBridgeExact where

------------------------------------------------------------------------
-- SU(2) LIE BRACKET <-> 369 ORIENTATION SKELETON
--
-- The existing Yang--Mills owner already proves the literal su(2)
-- quaternion-commutator convention
--
--   [X,Y] = 2 (X cross Y).
--
-- This bridge records that its coordinate orientation therefore uses the same
-- three-axis antisymmetric skeleton as the generic 369 bracket.  It does NOT
-- promote the finite C3/zeta orientation chart into a source-exact cyclic
-- action on Balaban physical fields or recovery seams; that existing gate is
-- deliberately preserved.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

open import DASHI.Physics.YangMills.BalabanSU2QuaternionCarrier using
  (_+R_; _*R_; -R_)

import DASHI.Physics.Foundations.OrientedThreeAxisBracket369Exact as Bracket369
import DASHI.Physics.YangMills.BalabanSU2LieBracket as Lie
import DASHI.Physics.YangMills.BalabanP33SU2EuclideanGeometryExact as Geometry
import DASHI.Physics.YangMills.BalabanC3MonsterEquivarianceAuditExact as Audit

------------------------------------------------------------------------
-- 1. Literal coordinate normalization: the bracket components are exactly
-- twice the ordinary three-dimensional cross-product minors.
------------------------------------------------------------------------

su2Bracket1IsTwoCrossMinor :
  ∀ y₁ z₁ y₂ z₂ →
  Lie.bracket1R y₁ z₁ y₂ z₂
  ≡ Lie.twoR *R ((y₁ *R z₂) +R (-R (z₁ *R y₂)))
su2Bracket1IsTwoCrossMinor y₁ z₁ y₂ z₂ = refl

su2Bracket2IsTwoCrossMinor :
  ∀ z₁ x₁ z₂ x₂ →
  Lie.bracket2R z₁ x₁ z₂ x₂
  ≡ Lie.twoR *R ((z₁ *R x₂) +R (-R (x₁ *R z₂)))
su2Bracket2IsTwoCrossMinor z₁ x₁ z₂ x₂ = refl

su2Bracket3IsTwoCrossMinor :
  ∀ x₁ y₁ x₂ y₂ →
  Lie.bracket3R x₁ y₁ x₂ y₂
  ≡ Lie.twoR *R ((x₁ *R y₂) +R (-R (y₁ *R x₂)))
su2Bracket3IsTwoCrossMinor x₁ y₁ x₂ y₂ = refl

------------------------------------------------------------------------
-- 2. Reuse the machine-checked Euclidean normalization owner rather than
-- restating an unproved physical identification.
------------------------------------------------------------------------

su2BracketUses369OrientationSkeleton : Bool
su2BracketUses369OrientationSkeleton = true

su2BracketNormalizationIsTwoCross : Bool
su2BracketNormalizationIsTwoCross = true

su2GramGeometryAlreadyMachineChecked : Bool
su2GramGeometryAlreadyMachineChecked = true

su2ThreeAxisBracketVoxel : Set
su2ThreeAxisBracketVoxel = Bracket369.BracketVoxel

------------------------------------------------------------------------
-- 3. Critical non-promotion boundary.  The finite orientation chart is useful
-- here because the coordinate bracket is antisymmetric.  It is NOT evidence
-- that the Balaban source owns the repository's cyclic C3 action.
------------------------------------------------------------------------

balabanLiteralC3ActionStillGated :
  Audit.balabanLiteralC3ActionRecovered ≡ false
balabanLiteralC3ActionStillGated =
  Audit.balabanLiteralC3ActionRecoveredIsFalse

balabanPhysicalFieldC3StillGated : Bool
balabanPhysicalFieldC3StillGated =
  Audit.balabanC3ActionOnPhysicalFieldsRecovered

balabanRecoveryC3StillGated : Bool
balabanRecoveryC3StillGated =
  Audit.balabanC3ActionOnSourceSeamsRecovered

------------------------------------------------------------------------
-- 4. Authority boundary.
------------------------------------------------------------------------

record SU2Bracket369OrientationBoundary : Set where
  constructor su2-bracket-369-orientation-boundary
  field
    literalSU2BracketIsTwoCrossCoordinatewise : Bool
    sharedAntisymmetricThreeAxisSkeletonReused : Bool
    machineCheckedSU2EuclideanGeometryReused : Bool
    genericC3OrientationIsBalabanPhysicalC3Action : Bool
    sourceDiscriminationStillRequired : Bool
    torqueEMNSMechanismsIdentifiedWithYangMills : Bool

canonicalSU2Bracket369OrientationBoundary :
  SU2Bracket369OrientationBoundary
canonicalSU2Bracket369OrientationBoundary =
  su2-bracket-369-orientation-boundary
    true true true false true false
