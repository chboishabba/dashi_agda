module DASHI.Analysis.RiemannG2C3SimultaneousDeterminantCovariance369Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)
open import Relation.Binary.PropositionalEquality using (cong₂)

import DASHI.Analysis.RiemannG21AugmentedDeterminantFiniteExact as Finite
import DASHI.Analysis.RiemannG2C3FixedNuisanceDeterminantNoGo369Exact as FixedNoGo
import DASHI.Core.ThreeChannelC3EquivarianceGateExact as C3
import DASHI.Core.ConsumerRelativeSymmetryRelevanceExact as Symmetry
import DASHI.Core.ConsumerDescentMinimalObserverExact as Descent
import DASHI.Core.FrontierRelationStrengthBidiExact as Relation

------------------------------------------------------------------------
-- SIMULTANEOUS C3 COVARIANCE OF THE FINITE DETERMINANT CODE
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

------------------------------------------------------------------------
-- Package the exact finite covariance in the same generic C3/consumer language
-- used by the Base369/Monster cross-pollination gate.
------------------------------------------------------------------------

RowTriple : Set
RowTriple = Finite.Vec3 × (Finite.Vec3 × Finite.Vec3)

rotateRowTriple : RowTriple -> RowTriple
rotateRowTriple (a , (b , c)) =
  FixedNoGo.rotateVec3 a ,
  (FixedNoGo.rotateVec3 b , FixedNoGo.rotateVec3 c)

rotateRowTripleCubed : (rows : RowTriple) ->
  rotateRowTriple (rotateRowTriple (rotateRowTriple rows)) ≡ rows
rotateRowTripleCubed (a , (b , c))
  rewrite FixedNoGo.rotateVec3Cubed a
        | FixedNoGo.rotateVec3Cubed b
        | FixedNoGo.rotateVec3Cubed c = refl

finiteRowTripleC3Action : C3.OrderThreeAction RowTriple
finiteRowTripleC3Action = record
  { rotate = rotateRowTriple
  ; rotateCubed = rotateRowTripleCubed
  }

rowTripleDeterminantObserver : RowTriple -> Finite.OrientedDet3Code
rowTripleDeterminantObserver (a , (b , c)) = Finite.det3 a b c

rowTripleRotationPreservesDeterminantObserver :
  Symmetry.PreservesObserver rowTripleDeterminantObserver rotateRowTriple
rowTripleRotationPreservesDeterminantObserver (a , (b , c)) =
  sym (simultaneousRotationPreservesDeterminantCode a b c)

anyDeterminantSufficientConsumerIsInvariantUnderSimultaneousC3 :
  ∀ {Outcome : Set}
    (consumer : RowTriple -> Outcome) ->
  Descent.ConsumerSufficient rowTripleDeterminantObserver consumer ->
  Symmetry.ConsumerInvariantUnder consumer rotateRowTriple
anyDeterminantSufficientConsumerIsInvariantUnderSimultaneousC3 consumer sufficient =
  Symmetry.sufficientObserverPreservationImpliesConsumerInvariance
    sufficient
    rowTripleRotationPreservesDeterminantObserver

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
    simultaneousRotationIsPackagedAsOrderThreeAction : Bool
    simultaneousRotationIsPackagedAsOrderThreeActionIsTrue :
      simultaneousRotationIsPackagedAsOrderThreeAction ≡ true
    determinantSufficientConsumersInvariantUnderFiniteC3 : Bool
    determinantSufficientConsumersInvariantUnderFiniteC3IsTrue :
      determinantSufficientConsumersInvariantUnderFiniteC3 ≡ true
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
    true refl
    true refl
    false refl
    true refl
    "The viable C3 shape is covariant rotation of the whole determinant geometry, not target-only channel rotation. On the finite row-triple carrier this is now an actual order-three action preserving the determinant observer, so every determinant-sufficient consumer is invariant automatically. The literal RH obligation is to weld the actual nuisance rows and taper response into this same-object action or abandon the C3 route."
