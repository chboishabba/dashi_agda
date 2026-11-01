module DASHI.Analysis.RiemannG2C3FixedNuisanceDeterminantNoGo369Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

import DASHI.Analysis.RiemannG21AugmentedDeterminantFiniteExact as Finite
import DASHI.Core.FrontierRelationStrengthBidiExact as Relation

------------------------------------------------------------------------
-- FIXED-NUISANCE C3 / DETERMINANT NO-GO FIXTURE
--
-- This is a finite exact regression of a structural warning relevant to G2:
-- cyclically rotating only the three coordinates of the target response does
-- not generically preserve det(n1,n2,h) when the nuisance rows n1,n2 are held
-- fixed.
--
-- It is NOT a theorem that the literal RH tapers lack C3 symmetry.  It proves
-- only that raw channel rotation plus fixed nuisances is not automatically a
-- determinant symmetry, so a literal q-invariance receipt cannot be omitted.
------------------------------------------------------------------------

rotateVec3 : Finite.Vec3 -> Finite.Vec3
rotateVec3 (x , (y , z)) = y , (z , x)

rotateVec3Cubed : (v : Finite.Vec3) ->
  rotateVec3 (rotateVec3 (rotateVec3 v)) ≡ v
rotateVec3Cubed (x , (y , z)) = refl

nuisanceOne nuisanceTwo targetCell : Finite.Vec3
nuisanceOne = 1 , (0 , 0)
nuisanceTwo = 0 , (1 , 0)
targetCell = 1 , (0 , 0)

originalTargetDeterminant :
  Finite.det3 nuisanceOne nuisanceTwo targetCell
  ≡ Finite.det3Code 0 0
originalTargetDeterminant = refl

rotatedTargetDeterminant :
  Finite.det3 nuisanceOne nuisanceTwo (rotateVec3 targetCell)
  ≡ Finite.det3Code 1 0
rotatedTargetDeterminant = refl

fixedNuisanceTargetRotationDoesNotPreserveDeterminant :
  Finite.det3 nuisanceOne nuisanceTwo (rotateVec3 targetCell)
  ≡ Finite.det3 nuisanceOne nuisanceTwo targetCell
  -> ⊥
fixedNuisanceTargetRotationDoesNotPreserveDeterminant ()

rawChannelRotationNotAutomaticallyQInvariant : Bool
rawChannelRotationNotAutomaticallyQInvariant = true

fixedNuisanceC3NoGoRelation : Relation.RelationKind
fixedNuisanceC3NoGoRelation = Relation.provedSearchObstructionReuse

fixedNuisanceC3NoGoReuse : Relation.ReuseCapability fixedNuisanceC3NoGoRelation
fixedNuisanceC3NoGoReuse = Relation.reuseProvedSearchObstruction

record FixedNuisanceC3DeterminantBoundary : Set where
  constructor fixedNuisanceC3DeterminantBoundary
  field
    coordinateRotationHasOrderThree : Bool
    coordinateRotationHasOrderThreeIsTrue : coordinateRotationHasOrderThree ≡ true
    rotatingTargetAloneAutomaticallyPreservesDeterminant : Bool
    rotatingTargetAloneAutomaticallyPreservesDeterminantIsFalse :
      rotatingTargetAloneAutomaticallyPreservesDeterminant ≡ false
    literalRHC3SymmetryRuledOutByFiniteFixture : Bool
    literalRHC3SymmetryRuledOutByFiniteFixtureIsFalse :
      literalRHC3SymmetryRuledOutByFiniteFixture ≡ false
    literalQInvarianceStillRequiresSameObjectProof : Bool
    literalQInvarianceStillRequiresSameObjectProofIsTrue :
      literalQInvarianceStillRequiresSameObjectProof ≡ true
    highestAlphaReading : String

canonicalFixedNuisanceC3DeterminantBoundary : FixedNuisanceC3DeterminantBoundary
canonicalFixedNuisanceC3DeterminantBoundary =
  fixedNuisanceC3DeterminantBoundary
    true refl
    false refl
    false refl
    true refl
    "A bare C3 rotation of the target/taper coordinates is not enough when the two nuisance rows are fixed: the determinant can change. Any RH symmetry route must therefore rotate the nuisance geometry compatibly or prove an independent invariant/character law for q."
