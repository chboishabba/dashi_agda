module DASHI.Moonshine.P37MarkedDeckIsotypicCollisionExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Jean-Pierre Serre,
-- "Linear Representations of Finite Groups", Springer, 1977.
-- DOI: 10.1007/978-1-4684-9458-7.
-- Isotypic decomposition of the regular S3 representation.
--
-- Nicholas M. Katz and Barry Mazur,
-- "Arithmetic Moduli of Elliptic Curves", Princeton University Press, 1985.
-- DOI: 10.1515/9781400881710.
-- Full-level-2 deck action.
--
-- Adel Betina and Emmanuel Lecouturier,
-- "Congruence formulae for Legendre modular polynomials",
-- Journal of Number Theory 188 (2018), 71--87.
-- DOI: 10.1016/j.jnt.2018.01.006.
-- Marked Legendre Hecke/Frobenius context.
--
-- DASHI CONTRIBUTION
--
-- PR #585 already exhibits two actual p=37 marked observables with the same
-- scalar fingerprint (T3,T5,F)=(1,0,+1) but different deck behaviour.
-- P37MarkedDeckIsotypicJointDecompositionExact computes the complete deck
-- blocks from the source-native permutation orbitals.  This file identifies
-- the collision structurally inside those blocks:
--
--   * the deck-trivial block has eigenvector (-2,1,1);
--   * the standard multiplicity block has eigenvector
--         ((1,-2),(1,1),(1,1));
--   * both have exact fingerprint (1,0,+1).
--
-- Since the full standard isotypic component contains two copies of the
-- six-dimensional multiplicity block, the second mode is genuinely standard
-- deck type, not another coarse/trivial mode.
--
-- This is the non-Ogg p=37 analogue of the p=11 Brandt-vs-standard collision.
-- It shows that adding source-native marked Hecke and Frobenius does not by
-- itself recover auxiliary deck representation type.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Rational using (ℚ; _/_; -_)

import DASHI.Moonshine.P37MarkedDeckIsotypicJointDecompositionExact as Iso
import DASHI.Moonshine.P11MarkedX2S3HeckeDecompositionExact as P11

------------------------------------------------------------------------
-- p=37 deck-trivial collision line.
------------------------------------------------------------------------

p37TrivialCollisionVector : Iso.Block3
p37TrivialCollisionVector = Iso.block3 (- (+ 2 / 1)) (+ 1 / 1) (+ 1 / 1)

p37TrivialT3EigenOne :
  Iso.trivialT3 p37TrivialCollisionVector ≡ p37TrivialCollisionVector
p37TrivialT3EigenOne = refl

p37TrivialT5EigenZero :
  Iso.trivialT5 p37TrivialCollisionVector ≡ Iso.block3 (+ 0 / 1) (+ 0 / 1) (+ 0 / 1)
p37TrivialT5EigenZero = refl

p37TrivialFrobeniusEven :
  Iso.trivialF p37TrivialCollisionVector ≡ p37TrivialCollisionVector
p37TrivialFrobeniusEven = refl

------------------------------------------------------------------------
-- p=37 standard-deck collision multiplicity line.
------------------------------------------------------------------------

p37StandardCollisionVector : Iso.StdBlock3
p37StandardCollisionVector =
  Iso.stdBlock3
    (Iso.std2 (+ 1 / 1) (- (+ 2 / 1)))
    (Iso.std2 (+ 1 / 1) (+ 1 / 1))
    (Iso.std2 (+ 1 / 1) (+ 1 / 1))

p37StandardT3EigenOne :
  Iso.standardT3 p37StandardCollisionVector ≡ p37StandardCollisionVector
p37StandardT3EigenOne = refl

p37StandardT5EigenZero :
  Iso.standardT5 p37StandardCollisionVector
  ≡ Iso.stdBlock3
      (Iso.std2 (+ 0 / 1) (+ 0 / 1))
      (Iso.std2 (+ 0 / 1) (+ 0 / 1))
      (Iso.std2 (+ 0 / 1) (+ 0 / 1))
p37StandardT5EigenZero = refl

p37StandardFrobeniusEven :
  Iso.standardF p37StandardCollisionVector ≡ p37StandardCollisionVector
p37StandardFrobeniusEven = refl

------------------------------------------------------------------------
-- Fingerprint and deck-type distinction.
------------------------------------------------------------------------

record ScalarJointFingerprint : Set where
  constructor scalarFingerprint
  field
    t3 t5 frobenius : ℤ

p37TrivialFingerprint p37StandardFingerprint : ScalarJointFingerprint
p37TrivialFingerprint = scalarFingerprint (+ 1) (+ 0) (+ 1)
p37StandardFingerprint = scalarFingerprint (+ 1) (+ 0) (+ 1)

p37ArithmeticFingerprintsCoincide :
  p37TrivialFingerprint ≡ p37StandardFingerprint
p37ArithmeticFingerprintsCoincide = refl

data DeckType : Set where
  deckTrivial deckStandard : DeckType

p37CollisionDeckTypesDiffer : deckTrivial ≡ deckStandard → ⊥
p37CollisionDeckTypesDiffer ()

record DeckRefinedFingerprint : Set where
  constructor deckRefined
  field
    scalar : ScalarJointFingerprint
    deck : DeckType

p37TrivialRefined p37StandardRefined : DeckRefinedFingerprint
p37TrivialRefined = deckRefined p37TrivialFingerprint deckTrivial
p37StandardRefined = deckRefined p37StandardFingerprint deckStandard

p37DeckRefinementSeparates : p37TrivialRefined ≡ p37StandardRefined → ⊥
p37DeckRefinementSeparates ()

------------------------------------------------------------------------
-- Cross-prime collision pattern.
--
-- p=11 carries the already-proved arithmetic collision (-1,1,+1) between the
-- coarse Brandt newform line and the deck-standard plane.  p=37 carries the
-- newly structurally explained collision (1,0,+1) between trivial and standard
-- deck blocks.  The numerical eigenvalues differ; the information-loss pattern
-- is the common invariant.
------------------------------------------------------------------------

p11ArithmeticCollisionStillExact :
  P11.brandtNewformFingerprint ≡ P11.standardFingerprint
p11ArithmeticCollisionStillExact = P11.brandtAndStandardFingerprintsCoincide

record CrossPrimeDeckBlindnessPattern : Set where
  field
    p11CoarseVsStandardScalarCollision : Bool
    p37TrivialVsStandardScalarCollision : Bool
    p37CollisionSeparatedByDeckType : Bool
    sameNumericalFingerprintAcrossPrimesClaimed : Bool
    markedHeckeFrobeniusDeterminesDeckTypeClaimed : Bool

canonicalCrossPrimeDeckBlindnessPattern : CrossPrimeDeckBlindnessPattern
canonicalCrossPrimeDeckBlindnessPattern = record
  { p11CoarseVsStandardScalarCollision = true
  ; p37TrivialVsStandardScalarCollision = true
  ; p37CollisionSeparatedByDeckType = true
  ; sameNumericalFingerprintAcrossPrimesClaimed = false
  ; markedHeckeFrobeniusDeterminesDeckTypeClaimed = false
  }
