module DASHI.Physics.Closure.ExtremalFrobeniusPrimitiveFixedPointLaw where

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.ExtremalFrobeniusFixedPointUniqueness as Uniqueness
import DASHI.Physics.Closure.ExtremalFrobeniusVacuumFixedPoint as Vacuum
import Ontology.GodelLattice as GL

------------------------------------------------------------------------
-- Primitive fixed-point law attempt.
--
-- No module named Vec15OrbitAction is present in this checkout.  The only
-- concrete action surface available to this lane is
-- ExtremalFrobeniusVacuumFixedPoint.canonicalExtremalFrobeniusActionSurface:
-- three coordinate permutations of the p47/p59/p71 tail.  Those permutations
-- cannot inhabit FixedPointFreeExtremalLaneAction, because the nonzero
-- diagonal tail (1,1,1) is fixed by all three.

one : Nat
one = suc zero

cong :
  {A B : Set} →
  (f : A → B) →
  {x y : A} →
  x ≡ y →
  f x ≡ f y
cong f refl =
  refl

one≠zero : one ≡ zero → ⊥
one≠zero ()

nonzeroDiagonalTail :
  GL.FactorVec
nonzeroDiagonalTail =
  GL.v15
    zero zero zero zero zero
    zero zero zero zero zero
    zero zero one one one

nonzeroDiagonalTail-p47 :
  GL.Vec15.e47 nonzeroDiagonalTail ≡ one
nonzeroDiagonalTail-p47 =
  refl

nonzeroDiagonalTail-p59 :
  GL.Vec15.e59 nonzeroDiagonalTail ≡ one
nonzeroDiagonalTail-p59 =
  refl

nonzeroDiagonalTail-p71 :
  GL.Vec15.e71 nonzeroDiagonalTail ≡ one
nonzeroDiagonalTail-p71 =
  refl

nonzeroDiagonalTailNotZero :
  nonzeroDiagonalTail ≡ Vacuum.zeroFactorVec →
  ⊥
nonzeroDiagonalTailNotZero diagonalIsZero =
  one≠zero (cong GL.Vec15.e47 diagonalIsZero)

nonzeroDiagonalTailP47Fixed :
  Vacuum.frobeniusP47Action nonzeroDiagonalTail
  ≡
  nonzeroDiagonalTail
nonzeroDiagonalTailP47Fixed =
  refl

nonzeroDiagonalTailP59Fixed :
  Vacuum.frobeniusP59Action nonzeroDiagonalTail
  ≡
  nonzeroDiagonalTail
nonzeroDiagonalTailP59Fixed =
  refl

nonzeroDiagonalTailP71Fixed :
  Vacuum.frobeniusP71Action nonzeroDiagonalTail
  ≡
  nonzeroDiagonalTail
nonzeroDiagonalTailP71Fixed =
  refl

canonicalPermutationActionCannotBeFixedPointFree :
  (law : Uniqueness.FixedPointFreeExtremalLaneAction) →
  Uniqueness.FixedPointFreeExtremalLaneAction.actionSurface law
    ≡
  Vacuum.canonicalExtremalFrobeniusActionSurface →
  ⊥
canonicalPermutationActionCannotBeFixedPointFree law actionIsCanonical =
  nonzeroDiagonalTailNotZero
    (Uniqueness.FixedPointFreeExtremalLaneAction.fixedByAllExtremalImpliesZero
      law
      nonzeroDiagonalTail
      p47Fixed
      p59Fixed
      p71Fixed)
  where
    p47Fixed :
      Vacuum.p47Action
        (Uniqueness.FixedPointFreeExtremalLaneAction.actionSurface law)
        nonzeroDiagonalTail
      ≡
      nonzeroDiagonalTail
    p47Fixed rewrite actionIsCanonical =
      nonzeroDiagonalTailP47Fixed

    p59Fixed :
      Vacuum.p59Action
        (Uniqueness.FixedPointFreeExtremalLaneAction.actionSurface law)
        nonzeroDiagonalTail
      ≡
      nonzeroDiagonalTail
    p59Fixed rewrite actionIsCanonical =
      nonzeroDiagonalTailP59Fixed

    p71Fixed :
      Vacuum.p71Action
        (Uniqueness.FixedPointFreeExtremalLaneAction.actionSurface law)
        nonzeroDiagonalTail
      ≡
      nonzeroDiagonalTail
    p71Fixed rewrite actionIsCanonical =
      nonzeroDiagonalTailP71Fixed

data ExtremalFrobeniusPrimitiveFixedPointLawMissing : Set where
  missingFiniteFieldPrimitiveRootFixedPointLaw :
    ExtremalFrobeniusPrimitiveFixedPointLawMissing

  missingVec15OrbitActionPrimitiveSemantics :
    ExtremalFrobeniusPrimitiveFixedPointLawMissing

  missingNonPermutationPrimitiveFrobeniusAction :
    ExtremalFrobeniusPrimitiveFixedPointLawMissing

canonicalExtremalFrobeniusPrimitiveFixedPointLawMissing :
  List ExtremalFrobeniusPrimitiveFixedPointLawMissing
canonicalExtremalFrobeniusPrimitiveFixedPointLawMissing =
  missingFiniteFieldPrimitiveRootFixedPointLaw
  ∷ missingVec15OrbitActionPrimitiveSemantics
  ∷ missingNonPermutationPrimitiveFrobeniusAction
  ∷ []

record ExtremalFrobeniusPrimitiveFixedPointLawReceipt : Set₂ where
  field
    uniquenessReceipt :
      Uniqueness.ExtremalFrobeniusFixedPointUniquenessReceipt

    uniquenessReceiptIsCanonical :
      uniquenessReceipt
      ≡
      Uniqueness.canonicalExtremalFrobeniusFixedPointUniquenessReceipt

    attemptedActionSurface :
      Vacuum.ExtremalFrobeniusActionSurface

    attemptedActionSurfaceIsCanonicalPermutation :
      attemptedActionSurface
      ≡
      Vacuum.canonicalExtremalFrobeniusActionSurface

    diagonalCounterexample :
      GL.FactorVec

    diagonalCounterexampleIsCanonical :
      diagonalCounterexample
      ≡
      nonzeroDiagonalTail

    diagonalCounterexampleP47Fixed :
      Vacuum.p47Action attemptedActionSurface diagonalCounterexample
      ≡
      diagonalCounterexample

    diagonalCounterexampleP59Fixed :
      Vacuum.p59Action attemptedActionSurface diagonalCounterexample
      ≡
      diagonalCounterexample

    diagonalCounterexampleP71Fixed :
      Vacuum.p71Action attemptedActionSurface diagonalCounterexample
      ≡
      diagonalCounterexample

    diagonalCounterexampleNotZero :
      diagonalCounterexample ≡ Vacuum.zeroFactorVec →
      ⊥

    canonicalPermutationActionObstruction :
      (law : Uniqueness.FixedPointFreeExtremalLaneAction) →
      Uniqueness.FixedPointFreeExtremalLaneAction.actionSurface law
        ≡
      attemptedActionSurface →
      ⊥

    fixedPointFreeLawInhabited :
      Bool

    fixedPointFreeLawInhabitedIsFalse :
      fixedPointFreeLawInhabited ≡ false

    exactMissingInhabitants :
      List ExtremalFrobeniusPrimitiveFixedPointLawMissing

    exactMissingInhabitantsAreCanonical :
      exactMissingInhabitants
      ≡
      canonicalExtremalFrobeniusPrimitiveFixedPointLawMissing

    firstMissingInhabitant :
      ExtremalFrobeniusPrimitiveFixedPointLawMissing

    firstMissingInhabitantIsFiniteFieldLaw :
      firstMissingInhabitant
      ≡
      missingFiniteFieldPrimitiveRootFixedPointLaw

    receiptBoundary :
      List String

canonicalExtremalFrobeniusPrimitiveFixedPointLawReceipt :
  ExtremalFrobeniusPrimitiveFixedPointLawReceipt
canonicalExtremalFrobeniusPrimitiveFixedPointLawReceipt =
  record
    { uniquenessReceipt =
        Uniqueness.canonicalExtremalFrobeniusFixedPointUniquenessReceipt
    ; uniquenessReceiptIsCanonical =
        refl
    ; attemptedActionSurface =
        Vacuum.canonicalExtremalFrobeniusActionSurface
    ; attemptedActionSurfaceIsCanonicalPermutation =
        refl
    ; diagonalCounterexample =
        nonzeroDiagonalTail
    ; diagonalCounterexampleIsCanonical =
        refl
    ; diagonalCounterexampleP47Fixed =
        nonzeroDiagonalTailP47Fixed
    ; diagonalCounterexampleP59Fixed =
        nonzeroDiagonalTailP59Fixed
    ; diagonalCounterexampleP71Fixed =
        nonzeroDiagonalTailP71Fixed
    ; diagonalCounterexampleNotZero =
        nonzeroDiagonalTailNotZero
    ; canonicalPermutationActionObstruction =
        canonicalPermutationActionCannotBeFixedPointFree
    ; fixedPointFreeLawInhabited =
        false
    ; fixedPointFreeLawInhabitedIsFalse =
        refl
    ; exactMissingInhabitants =
        canonicalExtremalFrobeniusPrimitiveFixedPointLawMissing
    ; exactMissingInhabitantsAreCanonical =
        refl
    ; firstMissingInhabitant =
        missingFiniteFieldPrimitiveRootFixedPointLaw
    ; firstMissingInhabitantIsFiniteFieldLaw =
        refl
    ; receiptBoundary =
        "No Vec15OrbitAction module is available in this checkout"
        ∷ "The concrete available action is the canonical p47/p59/p71 coordinate-permutation surface from ExtremalFrobeniusVacuumFixedPoint"
        ∷ "That concrete permutation action cannot inhabit FixedPointFreeExtremalLaneAction: the nonzero diagonal tail with p47=p59=p71=1 is fixed by all three actions"
        ∷ "Therefore fixedByAllExtremalImpliesZero is not provable for the currently modeled action"
        ∷ "First missing inhabitant is the finite-field primitive-root fixed-point law that replaces the permutation proxy by real primitive Frobenius semantics"
        ∷ "No postulate is introduced and no promotion flag is flipped"
        ∷ []
    }

primitiveFixedPointLawFirstMissing :
  ExtremalFrobeniusPrimitiveFixedPointLawReceipt.firstMissingInhabitant
    canonicalExtremalFrobeniusPrimitiveFixedPointLawReceipt
  ≡
  missingFiniteFieldPrimitiveRootFixedPointLaw
primitiveFixedPointLawFirstMissing =
  refl

primitiveFixedPointLawNotInhabited :
  ExtremalFrobeniusPrimitiveFixedPointLawReceipt.fixedPointFreeLawInhabited
    canonicalExtremalFrobeniusPrimitiveFixedPointLawReceipt
  ≡
  false
primitiveFixedPointLawNotInhabited =
  refl
