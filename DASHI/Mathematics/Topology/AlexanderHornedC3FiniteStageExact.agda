module DASHI.Mathematics.Topology.AlexanderHornedC3FiniteStageExact where

------------------------------------------------------------------------
-- ALEXANDER HORNED SPHERE / THREEFOLD SYMMETRY: FINITE ALGEBRA
--
-- SOURCES
-- Allen Hatcher, Algebraic Topology, Example 2B.2 (pp. 170--172):
-- https://pi.math.cornell.edu/~hatcher/AT/AT.pdf
-- J. W. Alexander (1924), classical horned sphere.
--
-- ORIGINAL FORMAL CONTRIBUTION
-- Reuse the pre-existing exact C3 action to act on three marked copies
-- of the binary horn-subdivision address tree.  Show, at the free-word
-- syntax level, that (1) the rotation has order three, (2) it commutes
-- with every finite horn replacement, (3) the permutation image of
-- the three-strand braid relation gives the same root rotation, and
-- (4) any C3-valued character satisfying the commutator replacement
-- relations vanishes on *every* generator.
--
-- CLAIM BOUNDARY
-- These are theorems about addresses and formal words.  In particular,
-- Word is NOT claimed to be the fundamental group of a complement.
-- No wild embedding, pi_1 calculation, geometric C3 action, or
-- nontrivial outer automorphism is derived in this file.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; trans)

import DASHI.Core.FiniteC3OrbitStabilizerExact as C3

_≢_ : ∀ {A : Set} → A → A → Set
x ≢ y = x ≡ y → ⊥

-- The address space is *three* copies of the binary horn tree.
-- Three is the orbit/symmetry count, NOT the branching arity.
data Bit : Set where
  left right : Bit

record HornAddress : Set where
  constructor address
  field
    sector : C3.C3
    suffix : List Bit

open HornAddress public

leftChild rightChild : HornAddress → HornAddress
leftChild  (address g xs) = address g (left ∷ xs)
rightChild (address g xs) = address g (right ∷ xs)

rotateSector : C3.C3 → C3.C3
rotateSector x = C3.act C3.c1 x

rotateSectorCubed : ∀ x →
  rotateSector (rotateSector (rotateSector x)) ≡ x
rotateSectorCubed C3.c0 = refl
rotateSectorCubed C3.c1 = refl
rotateSectorCubed C3.c2 = refl

rotateAddress : HornAddress → HornAddress
rotateAddress (address g xs) = address (rotateSector g) xs

rotateAddressCubed : ∀ a →
  rotateAddress (rotateAddress (rotateAddress a)) ≡ a
rotateAddressCubed (address C3.c0 xs) = refl
rotateAddressCubed (address C3.c1 xs) = refl
rotateAddressCubed (address C3.c2 xs) = refl

rotationRespectsLeftChild : ∀ a →
  rotateAddress (leftChild a) ≡ leftChild (rotateAddress a)
rotationRespectsLeftChild (address g xs) = refl

rotationRespectsRightChild : ∀ a →
  rotateAddress (rightChild a) ≡ rightChild (rotateAddress a)
rotationRespectsRightChild (address g xs) = refl

-- The three-strand braid group maps to S3 by strand permutation.
-- Its two standard generators give transpositions (01) and (12).
-- We only claim its *permutation image*, not a faithful B3 action.
swap01 swap12 : C3.C3 → C3.C3
swap01 C3.c0 = C3.c1
swap01 C3.c1 = C3.c0
swap01 C3.c2 = C3.c2
swap12 C3.c0 = C3.c0
swap12 C3.c1 = C3.c2
swap12 C3.c2 = C3.c1

braidRelationOnSectors : ∀ x →
  swap01 (swap12 (swap01 x))
    ≡ swap12 (swap01 (swap12 x))
braidRelationOnSectors C3.c0 = refl
braidRelationOnSectors C3.c1 = refl
braidRelationOnSectors C3.c2 = refl

braidProductIsC3Rotation : ∀ x →
  swap01 (swap12 x) ≡ rotateSector x
braidProductIsC3Rotation C3.c0 = refl
braidProductIsC3Rotation C3.c1 = refl
braidProductIsC3Rotation C3.c2 = refl

-- Words are deliberately unquotiented syntax.  The geometric
-- van Kampen/direct-limit identification remains a separate task.
data Word : Set where
  unit : Word
  generator : HornAddress → Word
  inverseWord : Word → Word
  combine : Word → Word → Word

commutator : Word → Word → Word
commutator a b =
  combine (combine (combine a b) (inverseWord a)) (inverseWord b)

rotateWord : Word → Word
rotateWord unit = unit
rotateWord (generator a) = generator (rotateAddress a)
rotateWord (inverseWord a) = inverseWord (rotateWord a)
rotateWord (combine a b) = combine (rotateWord a) (rotateWord b)

rotateWordCubed : ∀ w →
  rotateWord (rotateWord (rotateWord w)) ≡ w
rotateWordCubed unit = refl
rotateWordCubed (generator (address C3.c0 xs)) = refl
rotateWordCubed (generator (address C3.c1 xs)) = refl
rotateWordCubed (generator (address C3.c2 xs)) = refl
rotateWordCubed (inverseWord w) = cong inverseWord (rotateWordCubed w)
rotateWordCubed (combine a b) =
  cong₂ combine (rotateWordCubed a) (rotateWordCubed b)

rotationMovesMarkedGenerator :
  rotateWord (generator (address C3.c0 []))
    ≢ generator (address C3.c0 [])
rotationMovesMarkedGenerator ()

-- Hatcher's replacement: each meridian generator maps to a
-- commutator of two meridians at the next stage.
expandWord : Word → Word
expandWord unit = unit
expandWord (generator a) =
  commutator (generator (leftChild a)) (generator (rightChild a))
expandWord (inverseWord w) = inverseWord (expandWord w)
expandWord (combine a b) = combine (expandWord a) (expandWord b)

rotationCommutesWithExpansion : ∀ w →
  rotateWord (expandWord w) ≡ expandWord (rotateWord w)
rotationCommutesWithExpansion unit = refl
rotationCommutesWithExpansion (generator (address g xs)) = refl
rotationCommutesWithExpansion (inverseWord w) =
  cong inverseWord (rotationCommutesWithExpansion w)
rotationCommutesWithExpansion (combine a b) =
  cong₂ combine
    (rotationCommutesWithExpansion a)
    (rotationCommutesWithExpansion b)

expandN : Nat → Word → Word
expandN zero w = w
expandN (suc n) w = expandWord (expandN n w)

rotationCommutesAtEveryFiniteStage : ∀ n w →
  rotateWord (expandN n w) ≡ expandN n (rotateWord w)
rotationCommutesAtEveryFiniteStage zero w = refl
rotationCommutesAtEveryFiniteStage (suc n) w =
  trans
    (rotationCommutesWithExpansion (expandN n w))
    (cong expandWord (rotationCommutesAtEveryFiniteStage n w))

-- An abelian detector is insufficient for Hatcher's exterior group.
-- This finite specialisation makes the obstruction fully explicit
-- for all C3-valued characters, not just the identity character.
commutatorC3 : C3.C3 → C3.C3 → C3.C3
commutatorC3 a b =
  C3._∙_
    (C3._∙_ (C3._∙_ a b) (C3.inverse a))
    (C3.inverse b)

everyC3CommutatorVanishes : ∀ a b →
  commutatorC3 a b ≡ C3.c0
everyC3CommutatorVanishes C3.c0 C3.c0 = refl
everyC3CommutatorVanishes C3.c0 C3.c1 = refl
everyC3CommutatorVanishes C3.c0 C3.c2 = refl
everyC3CommutatorVanishes C3.c1 C3.c0 = refl
everyC3CommutatorVanishes C3.c1 C3.c1 = refl
everyC3CommutatorVanishes C3.c1 C3.c2 = refl
everyC3CommutatorVanishes C3.c2 C3.c0 = refl
everyC3CommutatorVanishes C3.c2 C3.c1 = refl
everyC3CommutatorVanishes C3.c2 C3.c2 = refl

record CompatibleC3Character : Set where
  constructor compatibleC3Character
  field
    value : HornAddress → C3.C3
    respectsHornReplacement : ∀ a →
      value a ≡ commutatorC3
        (value (leftChild a)) (value (rightChild a))

open CompatibleC3Character public

everyCompatibleC3CharacterVanishes :
  (chi : CompatibleC3Character) → ∀ a →
    value chi a ≡ C3.c0
everyCompatibleC3CharacterVanishes chi a =
  trans
    (respectsHornReplacement chi a)
    (everyC3CommutatorVanishes
      (value chi (leftChild a))
      (value chi (rightChild a)))

-- Distinct concepts that must not be collapsed:
-- the C3 *action* on labelled finite-stage words is nontrivial;
-- any C3 *character* satisfying all horn relations is trivial.
