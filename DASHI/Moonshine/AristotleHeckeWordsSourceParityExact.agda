module DASHI.Moonshine.AristotleHeckeWordsSourceParityExact where

------------------------------------------------------------------------
-- UPSTREAM ARISTOTLE SOURCE / ATTRIBUTION
--
-- Aristotle (Harmonic), editor of the user-supplied Lean project.
-- Source module:
--   RequestProject.HeckeWords
--   SHA-256 893eaa885ca57e4698767e38903a02e20702086cb0661e64f295b504d2589a03
--
-- The upstream README requests @Aristotle-Harmonic attribution and the commit
-- trailer
--   Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>
--
-- PRIMARY MATHEMATICAL SOURCES / CONTEXT
--
-- Toshitsune Miyake,
-- "Modular Forms", Springer Monographs in Mathematics, Springer, 2006.
-- DOI: 10.1007/3-540-29593-3.
--
-- Jean-Pierre Serre,
-- "A Course in Arithmetic", Graduate Texts in Mathematics 7, Springer, 1973.
-- DOI: 10.1007/978-1-4684-9884-4.
--
-- DASHI CONTRIBUTION
--
-- Port the source's five Hecke words onto the repository's already-constructed
-- executable classical divisor-sum normalizer.  Instead of storing the five
-- answers independently, a word is a list of basis indices and is recursively
-- interpreted by repeated Hecke multiplication.
--
-- At weight k (represented by weightMinusOne = k-1), this computes:
--
--   T2             -> T2
--   T3             -> T3
--   T2 T3          -> T6
--   T2 T3 T2       -> T12 + 2^(k-1) T3
--   T3 T3 T3       -> T27 + (3^(k-1)+3^(k-1)) T3.
--
-- The last coefficient is the constructive Nat normal form of the source's
-- `2 * 3^(k-1)` echo.  At weight 12 it reduces exactly to 354294.
--
-- This is the formal-Hecke-algebra side of the Aristotle source, not merely
-- the previously imported Delta eigenvalue plate.  The generic CommRing/Finsupp
-- presentation used by Lean is not identified definitionally with this list
-- normal form; the theorem content is transported through the same classical
-- structure constants.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_)
open import Data.List.Base using (List; []; _∷_)

import DASHI.Moonshine.ClassicalHeckeWeightKSmallWordExact as Hecke

HeckeWord : Set
HeckeWord = List Nat

basis : Nat → Hecke.HeckeExpression
basis n = Hecke.heckeTerm 1 n ∷ []

normalizeWord : Nat → HeckeWord → Hecke.HeckeExpression
normalizeWord weightMinusOne [] = basis 1
normalizeWord weightMinusOne (index ∷ rest) =
  Hecke.combineAdjacentLikeTerms
    (Hecke.multiplyBasisByExpression
      weightMinusOne index (normalizeWord weightMinusOne rest))

wordTwo : HeckeWord
wordTwo = 2 ∷ []

wordThree : HeckeWord
wordThree = 3 ∷ []

wordTwoThree : HeckeWord
wordTwoThree = 2 ∷ 3 ∷ []

wordTwoThreeTwo : HeckeWord
wordTwoThreeTwo = 2 ∷ 3 ∷ 2 ∷ []

wordThreeThreeThree : HeckeWord
wordThreeThreeThree = 3 ∷ 3 ∷ 3 ∷ []

------------------------------------------------------------------------
-- Source word normal forms at arbitrary weight.
------------------------------------------------------------------------

normalizeWordTwo :
  (weightMinusOne : Nat) →
  normalizeWord weightMinusOne wordTwo
  ≡ basis 2
normalizeWordTwo weightMinusOne = refl

normalizeWordThree :
  (weightMinusOne : Nat) →
  normalizeWord weightMinusOne wordThree
  ≡ basis 3
normalizeWordThree weightMinusOne = refl

normalizeWordTwoThree :
  (weightMinusOne : Nat) →
  normalizeWord weightMinusOne wordTwoThree
  ≡ basis 6
normalizeWordTwoThree weightMinusOne = refl

normalizeWordTwoThreeTwo :
  (weightMinusOne : Nat) →
  normalizeWord weightMinusOne wordTwoThreeTwo
  ≡ Hecke.heckeTerm 1 12
      ∷ Hecke.heckeTerm (Hecke.powNat 2 weightMinusOne) 3
      ∷ []
normalizeWordTwoThreeTwo weightMinusOne = refl

normalizeWordThreeThreeThree :
  (weightMinusOne : Nat) →
  normalizeWord weightMinusOne wordThreeThreeThree
  ≡ Hecke.heckeTerm 1 27
      ∷ Hecke.heckeTerm
          (Hecke.powNat 3 weightMinusOne + Hecke.powNat 3 weightMinusOne) 3
      ∷ []
normalizeWordThreeThreeThree weightMinusOne = refl

------------------------------------------------------------------------
-- Exact weight-12 source plate.
------------------------------------------------------------------------

weight12WordTwoThreeTwo :
  normalizeWord 11 wordTwoThreeTwo
  ≡ Hecke.heckeTerm 1 12 ∷ Hecke.heckeTerm 2048 3 ∷ []
weight12WordTwoThreeTwo = refl

weight12WordThreeThreeThree :
  normalizeWord 11 wordThreeThreeThree
  ≡ Hecke.heckeTerm 1 27 ∷ Hecke.heckeTerm 354294 3 ∷ []
weight12WordThreeThreeThree = refl

------------------------------------------------------------------------
-- The old hand-written small-word functions agree with the recursive word
-- interpreter, preventing a second parallel formal-Hecke semantics.
------------------------------------------------------------------------

recursive232AgreesExisting :
  (weightMinusOne : Nat) →
  normalizeWord weightMinusOne wordTwoThreeTwo
  ≡ Hecke.hecke232 weightMinusOne
recursive232AgreesExisting weightMinusOne = refl

recursive333Weight12AgreesExisting :
  normalizeWord 11 wordThreeThreeThree
  ≡ Hecke.hecke333Weight12
recursive333Weight12AgreesExisting = refl

record AristotleHeckeWordsParityBoundary : Set where
  field
    recursiveWordInterpreterConstructed : Bool
    recursiveWordInterpreterConstructedIsTrue :
      recursiveWordInterpreterConstructed ≡ true

    fiveSourceWordNormalFormsConstructed : Bool
    fiveSourceWordNormalFormsConstructedIsTrue :
      fiveSourceWordNormalFormsConstructed ≡ true

    weight12EchoCoefficientsConstructed : Bool
    weight12EchoCoefficientsConstructedIsTrue :
      weight12EchoCoefficientsConstructed ≡ true

    leanFinsuppCarrierIdentifiedDefinitionally : Bool
    leanFinsuppCarrierIdentifiedDefinitionallyIsFalse :
      leanFinsuppCarrierIdentifiedDefinitionally ≡ false

canonicalAristotleHeckeWordsParityBoundary :
  AristotleHeckeWordsParityBoundary
canonicalAristotleHeckeWordsParityBoundary = record
  { recursiveWordInterpreterConstructed = true
  ; recursiveWordInterpreterConstructedIsTrue = refl
  ; fiveSourceWordNormalFormsConstructed = true
  ; fiveSourceWordNormalFormsConstructedIsTrue = refl
  ; weight12EchoCoefficientsConstructed = true
  ; weight12EchoCoefficientsConstructedIsTrue = refl
  ; leanFinsuppCarrierIdentifiedDefinitionally = false
  ; leanFinsuppCarrierIdentifiedDefinitionallyIsFalse = refl
  }
