module DASHI.Moonshine.P11P37MarkedDeckSelectorCutsetExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Andrew P. Ogg,
-- "Automorphismes de courbes modulaires",
-- Seminaire Delange-Pisot-Poitou 16 (1974-1975), expose 7.
-- MR 417184; no DOI asserted.
--
-- John F. R. Duncan and Ken Ono,
-- "The Jack Daniels Problem", Journal of Number Theory 161 (2016), 230--239.
-- DOI: 10.1016/j.jnt.2015.06.001.
--
-- Jean-Pierre Serre,
-- "Linear Representations of Finite Groups", Springer, 1977.
-- DOI: 10.1007/978-1-4684-9458-7.
--
-- DASHI CONTRIBUTION
--
-- The p=11 and p=37 marked calculations now make two different notions of
-- separation explicit:
--
--   (A) representation separation:
--       deck type refines scalar Hecke/Frobenius fingerprints;
--
--   (B) Ogg/control separation:
--       the coarse geometric Frobenius paired-orbit defect differs at 11/37.
--
-- These are not the same theorem.  In particular, scalar Hecke/Frobenius
-- blindness to deck type occurs at BOTH p=11 and non-Ogg p=37, so the need for
-- a deck observer is not itself an Ogg selector.
--
-- Conversely, the existing finite under-72 scan proves zero coarse Frobenius
-- pair defect agrees with Fricke saturation / the external Ogg label, but that
-- scan is derived from the same Fricke/class-number input family.  It therefore
-- identifies the right candidate invariant without becoming an independent
-- geometric all-prime proof.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Moonshine.P37MarkedDeckIsotypicCollisionExact as P37Iso
import DASHI.Moonshine.P11MarkedX2DeckCharacterSeparationExact as P11Deck
import DASHI.Moonshine.BrandtHeckeFrobeniusFrickeSelectorWeldExact as Selector
import DASHI.Moonshine.OggPrimeControlMatrixExact as Matrix

------------------------------------------------------------------------
-- Representation-level information loss/refinement exists on both sides.
------------------------------------------------------------------------

p37ScalarFingerprintCannotDetermineDeckType :
  P37Iso.p37TrivialFingerprint ≡ P37Iso.p37StandardFingerprint
p37ScalarFingerprintCannotDetermineDeckType = P37Iso.p37ArithmeticFingerprintsCoincide

p37DeckRefinementRepairsKnownCollision :
  P37Iso.p37TrivialRefined ≡ P37Iso.p37StandardRefined → ⊥
p37DeckRefinementRepairsKnownCollision = P37Iso.p37DeckRefinementSeparates

p11DeckRefinementRepairsKnownCollision :
  P11Deck.brandtExtendedFingerprint ≡ P11Deck.standardExtendedFingerprint → ⊥
p11DeckRefinementRepairsKnownCollision = P11Deck.extendedFingerprintsSeparate

------------------------------------------------------------------------
-- Coarse geometric Frobenius is the presently surviving 11/37 separator.
------------------------------------------------------------------------

p11CoarseFrobeniusPairDefect : Nat
p11CoarseFrobeniusPairDefect = Selector.frobeniusPairDefect Matrix.prime11

p37CoarseFrobeniusPairDefect : Nat
p37CoarseFrobeniusPairDefect = Selector.frobeniusPairDefect Matrix.prime37

p11DefectZero : p11CoarseFrobeniusPairDefect ≡ 0
p11DefectZero = Selector.p11FrobeniusPairDefectIsZero

p37DefectOne : p37CoarseFrobeniusPairDefect ≡ 1
p37DefectOne = Selector.p37FrobeniusPairDefectIsOne

coarseFrobeniusPairDefectSeparates11And37 :
  p11CoarseFrobeniusPairDefect ≡ p37CoarseFrobeniusPairDefect → ⊥
coarseFrobeniusPairDefectSeparates11And37 = Selector.p11AndP37FrobeniusDefectsDiffer

------------------------------------------------------------------------
-- Finite Ogg calibration and authority boundary.
------------------------------------------------------------------------

finiteUnder72SelectorMatchesExternalOgg :
  (prime : Matrix.OddPrimeCandidateUnder72) →
  Selector.finiteFrobeniusSelector prime ≡ Matrix.externalOggLabel prime
finiteUnder72SelectorMatchesExternalOgg = Selector.finiteFrobeniusSelectorMatchesExternalOgg

record P11P37MarkedDeckSelectorCutsetBoundary : Set where
  field
    p11ScalarHeckeFrobeniusNeedsDeckRefinement : Bool
    p37ScalarHeckeFrobeniusNeedsDeckRefinement : Bool
    deckRefinementIsThereforeOggSelector : Bool
    coarseFrobeniusPairDefectSeparates11And37 : Bool
    finiteUnder72ZeroDefectMatchesOgg : Bool
    finiteScanIsIndependentGeometricAllPrimeProof : Bool
    nextIndependentControlGeometryNeeded : Bool

canonicalP11P37MarkedDeckSelectorCutsetBoundary :
  P11P37MarkedDeckSelectorCutsetBoundary
canonicalP11P37MarkedDeckSelectorCutsetBoundary = record
  { p11ScalarHeckeFrobeniusNeedsDeckRefinement = true
  ; p37ScalarHeckeFrobeniusNeedsDeckRefinement = true
  ; deckRefinementIsThereforeOggSelector = false
  ; coarseFrobeniusPairDefectSeparates11And37 = true
  ; finiteUnder72ZeroDefectMatchesOgg = true
  ; finiteScanIsIndependentGeometricAllPrimeProof = false
  ; nextIndependentControlGeometryNeeded = true
  }
