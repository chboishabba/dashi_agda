module DASHI.Physics.Electromagnetism.RightHandRule369Exact where

------------------------------------------------------------------------
-- ELECTROMAGNETIC RIGHT-HAND RULE AS A 369 ORIENTED-BRACKET CONSUMER
--
-- The right-hand rule is represented here as the positive orientation of the
-- same ordered three-axis bracket used by the torque tranche.  The physical
-- amplitudes and constitutive laws remain in an independent vector-space model.
--
-- This module covers the common cross-product skeleton of
--
--   magnetic Lorentz force:       q (v x B)
--   force on a current element:   I (L x B)
--   magnetic-dipole torque:       mu x B
--   Poynting direction:           E x H
--
-- without identifying these four observables or importing non-abelian
-- Yang--Mills authority into ordinary U(1) electromagnetism.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Algebra.BalancedTernary as BT
import DASHI.Algebra.TriadicDepthOneCharacters as C3
import DASHI.Physics.Foundations.OrientedThreeAxisBracket369Exact as Bracket369
import DASHI.Physics.Electromagnetism.U1ElectromagneticApplicationExact as U1

------------------------------------------------------------------------
-- 1. Abstract physical cross-product model.  A concrete EM application must
-- supply its own vector/scalar carrier and algebraic laws.
------------------------------------------------------------------------

record CrossProductModel : Set₁ where
  constructor cross-product-model
  field
    Vector Scalar : Set
    zeroVector : Vector
    negateVector : Vector → Vector
    scale : Scalar → Vector → Vector
    cross : Vector → Vector → Vector

    crossSwap :
      (a b : Vector) →
      cross b a ≡ negateVector (cross a b)

    crossSelfZero :
      (a : Vector) →
      cross a a ≡ zeroVector

open CrossProductModel public

magneticLorentzForce :
  (model : CrossProductModel) →
  Scalar model → Vector model → Vector model → Vector model
magneticLorentzForce model charge velocity magneticField =
  scale model charge (cross model velocity magneticField)

currentElementMagneticForce :
  (model : CrossProductModel) →
  Scalar model → Vector model → Vector model → Vector model
currentElementMagneticForce model current lengthVector magneticField =
  scale model current (cross model lengthVector magneticField)

magneticDipoleTorque :
  (model : CrossProductModel) →
  Vector model → Vector model → Vector model
magneticDipoleTorque model magneticMoment magneticField =
  cross model magneticMoment magneticField

poyntingDirection :
  (model : CrossProductModel) →
  Vector model → Vector model → Vector model
poyntingDirection model electricField magneticFieldIntensity =
  cross model electricField magneticFieldIntensity

------------------------------------------------------------------------
-- 2. Exact finite right-hand orientation chart.
------------------------------------------------------------------------

xyzRightHandPositive :
  Bracket369.bracketOrientation Bracket369.xyzBracket ≡ BT.pos
xyzRightHandPositive = Bracket369.xyzOrientationPositive

xzyRightHandNegative :
  Bracket369.bracketOrientation Bracket369.xzyBracket ≡ BT.neg
xzyRightHandNegative = Bracket369.xzyOrientationNegative

repeatedAxisNeutral :
  Bracket369.bracketOrientation Bracket369.xxyBracket ≡ BT.zero
repeatedAxisNeutral = Bracket369.xxyOrientationNeutral

rightHandSwapNegatesOrientation :
  (voxel : Bracket369.BracketVoxel) →
  Bracket369.bracketOrientation (Bracket369.swapBracketInputs voxel)
  ≡ BT.negate (Bracket369.bracketOrientation voxel)
rightHandSwapNegatesOrientation =
  Bracket369.swapBracketInputsNegatesOrientation

rightHandSwapConjugatesPhase :
  (voxel : Bracket369.BracketVoxel) →
  Bracket369.bracketPhase (Bracket369.swapBracketInputs voxel)
  ≡ C3.conjugatePhase (Bracket369.bracketPhase voxel)
rightHandSwapConjugatesPhase =
  Bracket369.swapBracketInputsConjugatesPhase

------------------------------------------------------------------------
-- 3. Same orientation address, distinct physical consumers.
------------------------------------------------------------------------

data EMBracketKind : Set where
  lorentzMagnetic
  currentElementMagnetic
  dipoleTorque
  poyntingFlux : EMBracketKind

record EMOrientedBracketSample
    (Vector : Set) : Set₁ where
  constructor em-oriented-bracket-sample
  field
    kind : EMBracketKind
    geometry : Bracket369.BracketVoxel
    left right result : Vector

open EMOrientedBracketSample public

emSampleOrientation :
  ∀ {Vector} → EMOrientedBracketSample Vector → BT.Trit
emSampleOrientation sample =
  Bracket369.bracketOrientation (geometry sample)

------------------------------------------------------------------------
-- 4. U(1) / non-abelian promotion firewall inherited from the existing EM
-- application socket.
------------------------------------------------------------------------

nonAbelianClayDoesNotProveU1Application :
  U1.suNClayPromotionImported ≡ false
nonAbelianClayDoesNotProveU1Application =
  U1.suNClayPromotionImportedIsFalse

record RightHandRule369Boundary : Set where
  constructor right-hand-rule-369-boundary
  field
    rightHandRuleUsesShared369Orientation : Bool
    lorentzForceUsesCrossSkeleton : Bool
    currentElementForceUsesCrossSkeleton : Bool
    magneticDipoleTorqueUsesCrossSkeleton : Bool
    poyntingDirectionUsesCrossSkeleton : Bool
    reversalFlipsOrientation : Bool
    parallelOrRepeatedAxisIsNeutral : Bool
    sharedOrientationIdentifiesPhysicalObservable : Bool
    u1ElectromagnetismPromotedToNonAbelianYangMills : Bool

canonicalRightHandRule369Boundary : RightHandRule369Boundary
canonicalRightHandRule369Boundary =
  right-hand-rule-369-boundary
    true true true true true true true false false
