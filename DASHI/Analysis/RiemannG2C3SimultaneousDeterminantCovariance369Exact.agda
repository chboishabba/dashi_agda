module DASHI.Analysis.RiemannG2C3SimultaneousDeterminantCovariance369Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)
open import Relation.Binary.PropositionalEquality using (cong₂)

import DASHI.Analysis.RiemannG21AugmentedDeterminantFiniteExact as Finite
import DASHI.Analysis.RiemannG2C3FixedNuisanceDeterminantNoGo369Exact as FixedNoGo
import DASHI.Core.FrontierRelationStrengthBidiExact as Relation

------------------------------------------------------------------------
-- SIMULTANEOUS C3 COVARIANCE OF THE FINITE DETERMINANT CODE
--
-- The previous no-go proves that rotating only the target coordinates while
-- holding nuisance rows fixed need not preserve det(n1,n2,h).
--
-- Here we prove the complementary finite algebra fact: the same cyclic
-- coordinate rotation applied simultaneously to all three rows preserves the
-- oriented 3x3 determinant code.  This is the correct symmetry shape suggested
-- by the 369/Monster coordinate-rotation lane.
--
-- This remains a finite algebra regression.  It does not assert that the
-- literal RH nuisance rows and taper response are closed under this action.
------------------------------------------------------------------------

cyclicThreeSum : (a b c : Nat) ->
  a + b + c ≡ b + c + a
cyclicThreeSum a b c =
  trans (+-assoc a b c) (+-comm a (b + c))

cyclicThreeSumTwice : (a b c : Nat) ->
  a + b + c ≡ c + a + b
cyclicThreeSumTwice a b c =
  trans
    (cyclicThreeSum a b c)
    (cyclicThreeSum b c a)

simultaneousRotationPreservesDeterminantCode :
  (a b c : Finite.Vec3) ->
  Finite.det3 a b c
  ≡ Finite.det3
      (FixedNoGo.rotateVec3 a)
      (FixedNoGo.rotateVec3 b)
      (FixedNoGo.rotateVec3 c)
simultaneousRotationPreservesDeterminantCode
  (a1 , (a2 , a3))
  (b1 , (b2 , b3))
  (c1 , (c2 , c3)) =
  cong₂ Finite.det3Code
    (cyclicThreeSum
      (a1 * b2 * c3)
      (a2 * b3 * c1)
      (a3 * b1 * c2))
    (cyclicThreeSumTwice
      (a3 * b2 * c1)
      (a2 * b1 * c3)
      (a1 * b3 * c2))

simultaneousRotationHasOrderThree : (v : Finite.Vec3) ->
  FixedNoGo.rotateVec3
    (FixedNoGo.rotateVec3 (FixedNoGo.rotateVec3 v)) ≡ v
simultaneousRotationHasOrderThree = FixedNoGo.rotateVec3Cubed

c3CovariantDeterminantRelation : Relation.RelationKind
c3CovariantDeterminantRelation = Relation.provedSearchObstructionReuse

c3CovariantDeterminantReuse : Relation.ReuseCapability c3CovariantDeterminantRelation
c3CovariantDeterminantReuse = Relation.reuseProvedSearchObstruction

record SimultaneousC3DeterminantBoundary : Set where
  constructor simultaneousC3DeterminantBoundary
  field
    targetOnlyRotationAlwaysPreservesDeterminant : Bool
    targetOnlyRotationAlwaysPreservesDeterminantIsFalse :
      targetOnlyRotationAlwaysPreservesDeterminant ≡ false
    simultaneousCoordinateRotationPreservesFiniteDeterminantCode : Bool
    simultaneousCoordinateRotationPreservesFiniteDeterminantCodeIsTrue :
      simultaneousCoordinateRotationPreservesFiniteDeterminantCode ≡ true
    finiteCovarianceEstablishesLiteralRHC3Action : Bool
    finiteCovarianceEstablishesLiteralRHC3ActionIsFalse :
      finiteCovarianceEstablishesLiteralRHC3Action ≡ false
    literalRouteRequiresNuisanceAndTargetSameObjectCovariance : Bool
    literalRouteRequiresNuisanceAndTargetSameObjectCovarianceIsTrue :
      literalRouteRequiresNuisanceAndTargetSameObjectCovariance ≡ true
    highestAlphaReading : String

canonicalSimultaneousC3DeterminantBoundary : SimultaneousC3DeterminantBoundary
canonicalSimultaneousC3DeterminantBoundary =
  simultaneousC3DeterminantBoundary
    false refl
    true refl
    false refl
    true refl
    "The viable C3 shape is covariant rotation of the whole determinant geometry, not target-only channel rotation. The next literal RH obligation is therefore to ask whether the two nuisance rows and taper response arise in a common order-three orbit and whether that same-object action survives the analytic construction."
