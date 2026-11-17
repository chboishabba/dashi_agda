module DASHI.Biology.OggTernaryEquivariantLabellingNoGoExact where

open import DASHI.Core.Prelude

import DASHI.Biology.TriadicKernelLiftQuotientExact as Triadic
import DASHI.Biology.TernaryRotationReflectionSeparationExact as Ops
import DASHI.Biology.TernaryMonsterSymmetryCandidateExact as Monster

------------------------------------------------------------------------
-- Structural port of Aristotle's concrete Ogg obstruction:
--   Lean/Spine/OggGrid.lean
--
-- Aristotle proves the Ogg CM observer has class counts 5 + 9 + 1, hence a
-- unique ramified point, and derives that no fixed-point-free order-three
-- permutation preserving that observer can exist.  The theorem below extracts
-- exactly the reusable mechanism: a free 5 x 3 ternary shift cannot be
-- equivariantly bijected to a class-preserving target with a unique ramified
-- point.

data FiveIndex : Set where
  indexZero : FiveIndex
  indexOne : FiveIndex
  indexTwo : FiveIndex
  indexThree : FiveIndex
  indexFour : FiveIndex

InternalCell : Set
InternalCell = FiveIndex × Triadic.KernelTrit

internalShift : InternalCell → InternalCell
internalShift (i , t) = i , Ops.rotateTrit t

internalShiftFree :
  (x : InternalCell) → internalShift x ≡ x → ⊥
internalShiftFree (i , Triadic.negativeTrit) ()
internalShiftFree (i , Triadic.zeroTrit) ()
internalShiftFree (i , Triadic.positiveTrit) ()

internalCardinalityCode : Nat
internalCardinalityCode = 5 * 3

internalCardinalityIsFifteen : internalCardinalityCode ≡ 15
internalCardinalityIsFifteen = refl

oggPrimeCountIsFifteen :
  Monster.listCount Monster.canonicalOggPrimes ≡ 15
oggPrimeCountIsFifteen = Monster.canonicalOggPrimeCountIsFifteen

data CMClass : Set where
  splitClass : CMClass
  inertClass : CMClass
  ramifiedClass : CMClass

record OggObservedSystem : Set₁ where
  constructor oggObservedSystem
  field
    Label : Set
    classify : Label → CMClass
    ramifiedPoint : Label
    ramifiedCertificate : classify ramifiedPoint ≡ ramifiedClass
    ramifiedUnique :
      (x : Label) → classify x ≡ ramifiedClass → x ≡ ramifiedPoint
    action : Label → Label
    classPreserved :
      (x : Label) → classify (action x) ≡ classify x

open OggObservedSystem public

targetRamifiedPointFixed :
  (S : OggObservedSystem) →
  action S (ramifiedPoint S) ≡ ramifiedPoint S
targetRamifiedPointFixed S =
  ramifiedUnique S
    (action S (ramifiedPoint S))
    (trans (classPreserved S (ramifiedPoint S))
      (ramifiedCertificate S))

record EquivariantOggLabelling (S : OggObservedSystem) : Set where
  constructor equivariantOggLabelling
  field
    forward : InternalCell → Label S
    backward : Label S → InternalCell
    leftInverse : (x : InternalCell) → backward (forward x) ≡ x
    rightInverse : (y : Label S) → forward (backward y) ≡ y
    intertwines :
      (x : InternalCell) → forward (internalShift x) ≡ action S (forward x)

open EquivariantOggLabelling public

fixedTargetForcesFixedInternal :
  (S : OggObservedSystem) →
  (e : EquivariantOggLabelling S) →
  internalShift (backward e (ramifiedPoint S))
  ≡
  backward e (ramifiedPoint S)
fixedTargetForcesFixedInternal S e =
  trans
    (sym (leftInverse e (internalShift (backward e (ramifiedPoint S)))))
    (trans
      (cong (backward e)
        (trans
          (intertwines e (backward e (ramifiedPoint S)))
          (trans
            (cong (action S) (rightInverse e (ramifiedPoint S)))
            (trans
              (targetRamifiedPointFixed S)
              (sym (rightInverse e (ramifiedPoint S)))))))
      (leftInverse e (backward e (ramifiedPoint S)))

noFreeTernaryOggEquivariantLabelling :
  (S : OggObservedSystem) → EquivariantOggLabelling S → ⊥
noFreeTernaryOggEquivariantLabelling S e =
  internalShiftFree
    (backward e (ramifiedPoint S))
    (fixedTargetForcesFixedInternal S e)

record OggLabellingBoundary : Set where
  constructor oggLabellingBoundary
  field
    fifteenEqualsFiveTimesThreeSuppliesEquivariantLabelling : Bool
    fifteenEqualsFiveTimesThreeSuppliesEquivariantLabellingIsFalse :
      fifteenEqualsFiveTimesThreeSuppliesEquivariantLabelling ≡ false

    oggArithmeticAloneConstructsMonsterAction : Bool
    oggArithmeticAloneConstructsMonsterActionIsFalse :
      oggArithmeticAloneConstructsMonsterAction ≡ false

canonicalOggLabellingBoundary : OggLabellingBoundary
canonicalOggLabellingBoundary =
  oggLabellingBoundary false refl false refl
