module DASHI.Wikimedia.IbrahimMonsterFiveOrbitD4CharacterBridgeExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.Nat using (_+_; _*_)

import DASHI.Biology.TriadicKernelLiftQuotientExact as Triadic
import DASHI.Biology.TernaryMonsterSymmetryCandidateExact as Symmetry
import DASHI.Biology.D4NineCellOrbitCompressionExact as D4
import DASHI.Biology.D4IrrepPhysicalRoleExact as Roles
import DASHI.Wikimedia.IbrahimMonsterTernary27PhasePreservingFiveOrbitReductionExact as Reduction

------------------------------------------------------------------------
-- FIVE INNER INVERSION ORBITS / D4 CHARACTER BRIDGE
--
-- The phase-preserving T^3 reduction keeps one outer trit and quotients the
-- inner T^2 sheet by simultaneous sign inversion.  The inner quotient has the
-- five constructors already owned by Triadic.NineOrbit.
--
-- A five-element quotient is NOT automatically the five D4 irreducible types.
-- The correct bridge is representation-theoretic: let the usual D4 square
-- symmetries act on the five quotient orbits, compute the permutation
-- character, and decompose that 5-dimensional permutation representation.
--
-- The Python probe added beside this owner computes, on conjugacy classes
--
--   e, r^2, {r,r^3}, axis reflections, diagonal reflections,
--
-- the fixed-orbit character
--
--   (5, 5, 1, 3, 3)
--
-- and decomposes it as
--
--   3 A1 + B1 + B2.
--
-- This exactly matches the existing raw-nine decomposition after removing
-- the two E copies:
--
--   raw 9 : 3 A1 + B1 + B2 + 2 E
--   quotient 5 : 3 A1 + B1 + B2.
--
-- Therefore the five quotient points should not be named one-to-one by the
-- five irrep species.  The quotient carries a 5-dimensional D4 permutation
-- representation whose isotypic content is the statement above.  A2 remains
-- absent, consistently with the existing raw-nine result.
--
-- Runtime character arithmetic is not Agda kernel certification and none of
-- this supplies a Monster class-42d action.
------------------------------------------------------------------------

fiveInnerOrbits : List Triadic.NineOrbit
fiveInnerOrbits =
  Triadic.zeroOrbit
  ∷ Triadic.firstAxisOrbit
  ∷ Triadic.secondAxisOrbit
  ∷ Triadic.equalSignOrbit
  ∷ Triadic.oppositeSignOrbit
  ∷ []

fiveInnerOrbitCountIsFive : D4.listCount fiveInnerOrbits ≡ 5
fiveInnerOrbitCountIsFive = refl

permutationCharacter : List Nat
permutationCharacter = 5 ∷ 5 ∷ 1 ∷ 3 ∷ 3 ∷ []

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

quotientRepresentationDimension : Nat
quotientRepresentationDimension =
  quotientA1Multiplicity * Symmetry.irrepDimension Symmetry.A1
  + quotientA2Multiplicity * Symmetry.irrepDimension Symmetry.A2
  + quotientB1Multiplicity * Symmetry.irrepDimension Symmetry.B1
  + quotientB2Multiplicity * Symmetry.irrepDimension Symmetry.B2
  + quotientEMultiplicity * Symmetry.irrepDimension Symmetry.E2

quotientRepresentationDimensionIsFive : quotientRepresentationDimension ≡ 5
quotientRepresentationDimensionIsFive = refl

rawNineA1Multiplicity : Nat
rawNineA1Multiplicity = Symmetry.rawNineMultiplicity Symmetry.A1

rawNineA2Multiplicity : Nat
rawNineA2Multiplicity = Symmetry.rawNineMultiplicity Symmetry.A2

rawNineB1Multiplicity : Nat
rawNineB1Multiplicity = Symmetry.rawNineMultiplicity Symmetry.B1

rawNineB2Multiplicity : Nat
rawNineB2Multiplicity = Symmetry.rawNineMultiplicity Symmetry.B2

rawNineEMultiplicity : Nat
rawNineEMultiplicity = Symmetry.rawNineMultiplicity Symmetry.E2

rawNineA1IsThree : rawNineA1Multiplicity ≡ 3
rawNineA1IsThree = refl

rawNineA2IsZero : rawNineA2Multiplicity ≡ 0
rawNineA2IsZero = Symmetry.rawA2MultiplicityIsZero

rawNineB1IsOne : rawNineB1Multiplicity ≡ 1
rawNineB1IsOne = refl

rawNineB2IsOne : rawNineB2Multiplicity ≡ 1
rawNineB2IsOne = refl

rawNineEIsTwo : rawNineEMultiplicity ≡ 2
rawNineEIsTwo = refl

removedECopyCount : Nat
removedECopyCount = rawNineEMultiplicity

removedEDimension : Nat
removedEDimension = removedECopyCount * Symmetry.irrepDimension Symmetry.E2

removedEDimensionIsFour : removedEDimension ≡ 4
removedEDimensionIsFour = refl

nineMinusFourIsFive : 9 ∸ removedEDimension ≡ 5
nineMinusFourIsFive = refl

------------------------------------------------------------------------
-- Existing semantic-role anchors.  These are deliberately not used to assign
-- individual quotient points to irrep names.
------------------------------------------------------------------------

invariantRoleAnchor : Roles.modeRole Symmetry.A1 ≡ Roles.invariantGlobalRole
invariantRoleAnchor = refl

orientationRoleAnchor :
  Roles.modeRole Symmetry.A2 ≡ Roles.orientationPseudoscalarRole
orientationRoleAnchor = refl

axialRoleAnchor : Roles.modeRole Symmetry.B1 ≡ Roles.axialContrastRole
axialRoleAnchor = refl

diagonalRoleAnchor : Roles.modeRole Symmetry.B2 ≡ Roles.diagonalContrastRole
diagonalRoleAnchor = refl

directionalRoleAnchor : Roles.modeRole Symmetry.E2 ≡ Roles.directionalPairRole
directionalRoleAnchor = refl

reductionBoundary : Reduction.Ternary27PhasePreservingReductionBoundary
reductionBoundary = Reduction.currentTernary27PhasePreservingReductionBoundary

------------------------------------------------------------------------
-- WrongType firewalls.
------------------------------------------------------------------------

data FiveOrbitCountCreatesFiveIrrepBijection : Set where
data PythonCharacterCreatesAgdaKernelTheorem : Set where
data D4CharacterCreatesMonster42dAction : Set where

data QuotientRemovesEThereforeMonsterIdentification : Set where

fiveOrbitCountDoesNotCreateFiveIrrepBijection :
  FiveOrbitCountCreatesFiveIrrepBijection → ⊥
fiveOrbitCountDoesNotCreateFiveIrrepBijection ()

pythonCharacterDoesNotCreateAgdaKernelTheorem :
  PythonCharacterCreatesAgdaKernelTheorem → ⊥
pythonCharacterDoesNotCreateAgdaKernelTheorem ()

d4CharacterDoesNotCreateMonster42dAction :
  D4CharacterCreatesMonster42dAction → ⊥
d4CharacterDoesNotCreateMonster42dAction ()

quotientRemovingEDoesNotCreateMonsterIdentification :
  QuotientRemovesEThereforeMonsterIdentification → ⊥
quotientRemovingEDoesNotCreateMonsterIdentification ()

------------------------------------------------------------------------
-- Receipt boundary.
------------------------------------------------------------------------

record FiveOrbitD4CharacterBoundary : Set where
  constructor five-orbit-d4-character-boundary
  field
    fiveInnerInversionOrbitSourcePaid : Bool
    d4RawNineRepresentationSourcePaid : Bool
    pythonCharacterProbeSourceWritten : Bool
    equivalentFiniteProbeObserved : Bool
    exactCommittedPytestObserved : Bool
    permutationCharacterFiveFiveOneThreeThreeRetained : Bool
    quotientDecompositionThreeA1B1B2Retained : Bool
    rawNineToQuotientRemovesTwoECopies : Bool
    a2AbsentOnRawNineAndQuotient : Bool
    fiveOrbitsAreFiveIrrepsOneToOne : Bool
    agdaKernelCharacterDecompositionObserved : Bool
    characterBridgeCreatesMonster42dAction : Bool
    nextResidual : String
open FiveOrbitD4CharacterBoundary public

currentFiveOrbitD4CharacterBoundary : FiveOrbitD4CharacterBoundary
currentFiveOrbitD4CharacterBoundary =
  five-orbit-d4-character-boundary
    true true true true false
    true true true true
    false false false
    "Promote the five inner inversion orbits by their D4 permutation representation, not by a one-to-one orbit/irrep naming. The runtime character (5,5,1,3,3) decomposes as 3*A1+B1+B2 and exactly removes the two E copies from the raw nine-cell decomposition 3*A1+B1+B2+2*E. Next acquire or formalize the D4 action/character decomposition in Agda, then ask whether that quotient representation participates in the selected Monster class-42d or N(3B) construction. OEIS/eta-level and same-integer evidence remain search coordinates only."
