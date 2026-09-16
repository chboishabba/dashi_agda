module DASHI.Wikimedia.IbrahimMonsterFiveOrbitD4KernelCharacterExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥)
open import Data.Nat using (_+_; _*_; _∸_)

import DASHI.Biology.TriadicKernelLiftQuotientExact as Triadic
import DASHI.Biology.TernaryMonsterSymmetryCandidateExact as Raw

------------------------------------------------------------------------
-- KERNEL-LEVEL D4 ACTION ON THE FIVE GLOBAL-INVERSION ORBITS
--
-- One nine-state sheet is T^2.  Triadic.quotientNine identifies x with -x,
-- leaving five global-inversion orbits.  The square symmetries descend to this
-- quotient.  In particular the 180-degree rotation is simultaneous negation,
-- so it acts trivially after quotienting; the descended D4 action is therefore
-- deliberately non-faithful.
------------------------------------------------------------------------

data D4Element : Set where
  e r r2 r3 sAxis sAxisR2 sDiag sDiagR2 : D4Element

rotateOrbit : Triadic.NineOrbit → Triadic.NineOrbit
rotateOrbit Triadic.zeroOrbit = Triadic.zeroOrbit
rotateOrbit Triadic.firstAxisOrbit = Triadic.secondAxisOrbit
rotateOrbit Triadic.secondAxisOrbit = Triadic.firstAxisOrbit
rotateOrbit Triadic.equalSignOrbit = Triadic.oppositeSignOrbit
rotateOrbit Triadic.oppositeSignOrbit = Triadic.equalSignOrbit

halfTurnOrbit : Triadic.NineOrbit → Triadic.NineOrbit
halfTurnOrbit o = o

reflectAxisOrbit : Triadic.NineOrbit → Triadic.NineOrbit
reflectAxisOrbit Triadic.zeroOrbit = Triadic.zeroOrbit
reflectAxisOrbit Triadic.firstAxisOrbit = Triadic.firstAxisOrbit
reflectAxisOrbit Triadic.secondAxisOrbit = Triadic.secondAxisOrbit
reflectAxisOrbit Triadic.equalSignOrbit = Triadic.oppositeSignOrbit
reflectAxisOrbit Triadic.oppositeSignOrbit = Triadic.equalSignOrbit

reflectDiagonalOrbit : Triadic.NineOrbit → Triadic.NineOrbit
reflectDiagonalOrbit Triadic.zeroOrbit = Triadic.zeroOrbit
reflectDiagonalOrbit Triadic.firstAxisOrbit = Triadic.secondAxisOrbit
reflectDiagonalOrbit Triadic.secondAxisOrbit = Triadic.firstAxisOrbit
reflectDiagonalOrbit Triadic.equalSignOrbit = Triadic.equalSignOrbit
reflectDiagonalOrbit Triadic.oppositeSignOrbit = Triadic.oppositeSignOrbit

act : D4Element → Triadic.NineOrbit → Triadic.NineOrbit
act e o = o
act r o = rotateOrbit o
act r2 o = halfTurnOrbit o
act r3 o = rotateOrbit o
act sAxis o = reflectAxisOrbit o
act sAxisR2 o = reflectAxisOrbit o
act sDiag o = reflectDiagonalOrbit o
act sDiagR2 o = reflectDiagonalOrbit o

rotateTwiceIsHalfTurn :
  (o : Triadic.NineOrbit) → rotateOrbit (rotateOrbit o) ≡ halfTurnOrbit o
rotateTwiceIsHalfTurn Triadic.zeroOrbit = refl
rotateTwiceIsHalfTurn Triadic.firstAxisOrbit = refl
rotateTwiceIsHalfTurn Triadic.secondAxisOrbit = refl
rotateTwiceIsHalfTurn Triadic.equalSignOrbit = refl
rotateTwiceIsHalfTurn Triadic.oppositeSignOrbit = refl

rotateFourIsIdentity :
  (o : Triadic.NineOrbit) →
  rotateOrbit (rotateOrbit (rotateOrbit (rotateOrbit o))) ≡ o
rotateFourIsIdentity Triadic.zeroOrbit = refl
rotateFourIsIdentity Triadic.firstAxisOrbit = refl
rotateFourIsIdentity Triadic.secondAxisOrbit = refl
rotateFourIsIdentity Triadic.equalSignOrbit = refl
rotateFourIsIdentity Triadic.oppositeSignOrbit = refl

axisReflectionInvolutive :
  (o : Triadic.NineOrbit) → reflectAxisOrbit (reflectAxisOrbit o) ≡ o
axisReflectionInvolutive Triadic.zeroOrbit = refl
axisReflectionInvolutive Triadic.firstAxisOrbit = refl
axisReflectionInvolutive Triadic.secondAxisOrbit = refl
axisReflectionInvolutive Triadic.equalSignOrbit = refl
axisReflectionInvolutive Triadic.oppositeSignOrbit = refl

diagonalReflectionInvolutive :
  (o : Triadic.NineOrbit) → reflectDiagonalOrbit (reflectDiagonalOrbit o) ≡ o
diagonalReflectionInvolutive Triadic.zeroOrbit = refl
diagonalReflectionInvolutive Triadic.firstAxisOrbit = refl
diagonalReflectionInvolutive Triadic.secondAxisOrbit = refl
diagonalReflectionInvolutive Triadic.equalSignOrbit = refl
diagonalReflectionInvolutive Triadic.oppositeSignOrbit = refl

axisConjugatesQuarterTurnToInverse :
  (o : Triadic.NineOrbit) →
  reflectAxisOrbit (rotateOrbit (reflectAxisOrbit o))
  ≡ rotateOrbit (rotateOrbit (rotateOrbit o))
axisConjugatesQuarterTurnToInverse Triadic.zeroOrbit = refl
axisConjugatesQuarterTurnToInverse Triadic.firstAxisOrbit = refl
axisConjugatesQuarterTurnToInverse Triadic.secondAxisOrbit = refl
axisConjugatesQuarterTurnToInverse Triadic.equalSignOrbit = refl
axisConjugatesQuarterTurnToInverse Triadic.oppositeSignOrbit = refl

------------------------------------------------------------------------
-- Permutation character: fixed quotient orbits by D4 element.
------------------------------------------------------------------------

fixedOrbitCount : D4Element → Nat
fixedOrbitCount e = 5
fixedOrbitCount r = 1
fixedOrbitCount r2 = 5
fixedOrbitCount r3 = 1
fixedOrbitCount sAxis = 3
fixedOrbitCount sAxisR2 = 3
fixedOrbitCount sDiag = 3
fixedOrbitCount sDiagR2 = 3

infixr 5 _∷ₙ_
_∷ₙ_ : Nat → List Nat → List Nat
_∷ₙ_ = _∷_

[]ₙ : List Nat
[]ₙ = []

quotientCharacterVector : List Nat
quotientCharacterVector =
  fixedOrbitCount e
  ∷ₙ fixedOrbitCount r2
  ∷ₙ fixedOrbitCount r
  ∷ₙ fixedOrbitCount sAxis
  ∷ₙ fixedOrbitCount sDiag
  ∷ₙ []ₙ

------------------------------------------------------------------------
-- D4 irreducible multiplicities and finite character reconstruction.
-- Class order used above:
--   e, r^2, {r,r^3}, axis reflections, diagonal reflections.
--
-- For 3 A1 + B1 + B2 the values are
--   5, 5, 3-1-1, 3+1-1, 3-1+1 = 5,5,1,3,3.
------------------------------------------------------------------------

quotientA1Multiplicity : Nat
quotientA1Multiplicity = 3

quotientA2Multiplicity : Nat
quotientA2Multiplicity = 0

quotientB1Multiplicity : Nat
quotientB1Multiplicity = 1

quotientB2Multiplicity : Nat
quotientB2Multiplicity = 1

quotientEMultiplicity : Nat
quotientEMultiplicity = 0

reconstructedIdentity : Nat
reconstructedIdentity =
  quotientA1Multiplicity + quotientA2Multiplicity
  + quotientB1Multiplicity + quotientB2Multiplicity
  + 2 * quotientEMultiplicity

reconstructedHalfTurn : Nat
reconstructedHalfTurn =
  (quotientA1Multiplicity + quotientA2Multiplicity
   + quotientB1Multiplicity + quotientB2Multiplicity)
  ∸ (2 * quotientEMultiplicity)

reconstructedQuarterTurn : Nat
reconstructedQuarterTurn =
  (quotientA1Multiplicity + quotientA2Multiplicity)
  ∸ (quotientB1Multiplicity + quotientB2Multiplicity)

reconstructedAxisReflection : Nat
reconstructedAxisReflection =
  (quotientA1Multiplicity + quotientB1Multiplicity)
  ∸ (quotientA2Multiplicity + quotientB2Multiplicity)

reconstructedDiagonalReflection : Nat
reconstructedDiagonalReflection =
  (quotientA1Multiplicity + quotientB2Multiplicity)
  ∸ (quotientA2Multiplicity + quotientB1Multiplicity)

reconstructedCharacterVector : List Nat
reconstructedCharacterVector =
  reconstructedIdentity
  ∷ₙ reconstructedHalfTurn
  ∷ₙ reconstructedQuarterTurn
  ∷ₙ reconstructedAxisReflection
  ∷ₙ reconstructedDiagonalReflection
  ∷ₙ []ₙ

reconstructedCharacterIsQuotientCharacter :
  reconstructedCharacterVector ≡ quotientCharacterVector
reconstructedCharacterIsQuotientCharacter = refl

------------------------------------------------------------------------
-- Raw-nine comparison.  Existing source multiplicities are
-- 3 A1 + B1 + B2 + 2 E.  Removing the two E copies changes only e/r^2;
-- on the quotient r^2 is simultaneous negation and hence acts trivially.
------------------------------------------------------------------------

rawA1 : Nat
rawA1 = Raw.rawNineMultiplicity Raw.A1

rawA2 : Nat
rawA2 = Raw.rawNineMultiplicity Raw.A2

rawB1 : Nat
rawB1 = Raw.rawNineMultiplicity Raw.B1

rawB2 : Nat
rawB2 = Raw.rawNineMultiplicity Raw.B2

rawE : Nat
rawE = Raw.rawNineMultiplicity Raw.E2

rawIdentity : Nat
rawIdentity = rawA1 + rawA2 + rawB1 + rawB2 + 2 * rawE

rawHalfTurn : Nat
rawHalfTurn = (rawA1 + rawA2 + rawB1 + rawB2) ∸ (2 * rawE)

rawQuarterTurn : Nat
rawQuarterTurn = (rawA1 + rawA2) ∸ (rawB1 + rawB2)

rawAxisReflection : Nat
rawAxisReflection = (rawA1 + rawB1) ∸ (rawA2 + rawB2)

rawDiagonalReflection : Nat
rawDiagonalReflection = (rawA1 + rawB2) ∸ (rawA2 + rawB1)

rawNineCharacterVector : List Nat
rawNineCharacterVector =
  rawIdentity
  ∷ₙ rawHalfTurn
  ∷ₙ rawQuarterTurn
  ∷ₙ rawAxisReflection
  ∷ₙ rawDiagonalReflection
  ∷ₙ []ₙ

removedECopies : Nat
removedECopies = rawE

removedEDimension : Nat
removedEDimension = removedECopies * Raw.irrepDimension Raw.E2

removedEDimensionIsFour : removedEDimension ≡ 4
removedEDimensionIsFour = refl

rawNineDimensionMinusRemovedEIsFive :
  Raw.rawNineRepresentationDimension ∸ removedEDimension ≡ 5
rawNineDimensionMinusRemovedEIsFive = refl

------------------------------------------------------------------------
-- Authority boundary.
------------------------------------------------------------------------

data KernelCharacterCreatesMonster42dAction : Set where
data FivePointCountCreatesFiveIrrepBijection : Set where

kernelCharacterDoesNotCreateMonster42dAction :
  KernelCharacterCreatesMonster42dAction → ⊥
kernelCharacterDoesNotCreateMonster42dAction ()

fivePointCountDoesNotCreateFiveIrrepBijection :
  FivePointCountCreatesFiveIrrepBijection → ⊥
fivePointCountDoesNotCreateFiveIrrepBijection ()

record FiveOrbitD4KernelCharacterBoundary : Set where
  constructor five-orbit-d4-kernel-character-boundary
  field
    quotientActionDefined : Bool
    d4GeneratorRelationsPaid : Bool
    fixedOrbitCharacterKernelWritten : Bool
    characterReconstructionKernelWritten : Bool
    quotientThreeA1B1B2Written : Bool
    rawNineTwoERemovalWritten : Bool
    fiveOrbitsAreFiveIrrepsOneToOne : Bool
    monster42dActionPaid : Bool
open FiveOrbitD4KernelCharacterBoundary public

currentFiveOrbitD4KernelCharacterBoundary : FiveOrbitD4KernelCharacterBoundary
currentFiveOrbitD4KernelCharacterBoundary =
  five-orbit-d4-kernel-character-boundary
    true true true true true true false false
