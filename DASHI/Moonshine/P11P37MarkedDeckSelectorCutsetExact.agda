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
-- The marked calculations make two different notions of separation explicit:
--
--   (A) representation separation:
--       deck type refines scalar Hecke/Frobenius fingerprints;
--
--   (B) Ogg/control separation:
--       the COARSE geometric Frobenius paired-orbit defect differs between the
--       Ogg p=11 laboratory and non-Ogg p=37/p=43 controls.
--
-- These are not the same theorem.  Scalar Hecke/Frobenius blindness to deck
-- type occurs at BOTH p=11 and non-Ogg p=37, so the need for a deck observer is
-- not itself an Ogg selector.
--
-- Independent/source-facing coarse Frobenius realizations now exist at:
--
--   p=11 : 2 fixed, 0 paired;
--   p=37 : 1 fixed, 1 paired;
--   p=43 : 2 fixed, 1 paired.
--
-- The p=43 realization is derived from an independent Deuring/full-level-2
-- chart with four coarse j-classes; it is not inferred from the Fricke table.
--
-- Conversely, the existing complete under-72 scan proves zero coarse
-- Frobenius pair defect agrees with Fricke saturation / the external Ogg label,
-- but that generic scan is derived from the same Fricke/class-number input
-- family.  It identifies the right candidate invariant without becoming an
-- independent geometric all-prime proof.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Moonshine.P37MarkedDeckIsotypicCollisionExact as P37Iso
import DASHI.Moonshine.P11MarkedX2DeckCharacterSeparationExact as P11Deck
import DASHI.Moonshine.BrandtHeckeFrobeniusFrickeSelectorWeldExact as Selector
import DASHI.Moonshine.OggPrimeControlMatrixExact as Matrix
import DASHI.Moonshine.SupersingularFrobeniusOrbitSpectrumExact as Spectrum
import DASHI.Moonshine.P37SageSupersingularFrobeniusExact as P37Geo
import DASHI.Moonshine.P43GeometricFrobeniusRealizationExact as P43Geo

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
-- Coarse geometric Frobenius is the presently surviving selector coordinate.
------------------------------------------------------------------------

p11CoarseFrobeniusPairDefect : Nat
p11CoarseFrobeniusPairDefect = Selector.frobeniusPairDefect Matrix.prime11

p37CoarseFrobeniusPairDefect : Nat
p37CoarseFrobeniusPairDefect = Selector.frobeniusPairDefect Matrix.prime37

p43CoarseFrobeniusPairDefect : Nat
p43CoarseFrobeniusPairDefect = Selector.frobeniusPairDefect Matrix.prime43

p11DefectZero : p11CoarseFrobeniusPairDefect ≡ 0
p11DefectZero = Selector.p11FrobeniusPairDefectIsZero

p37DefectOne : p37CoarseFrobeniusPairDefect ≡ 1
p37DefectOne = Selector.p37FrobeniusPairDefectIsOne

p43DefectOne : p43CoarseFrobeniusPairDefect ≡ 1
p43DefectOne = P43Geo.p43PairedOrbitDefectIsOne

coarseFrobeniusPairDefectSeparates11And37 :
  p11CoarseFrobeniusPairDefect ≡ p37CoarseFrobeniusPairDefect → ⊥
coarseFrobeniusPairDefectSeparates11And37 = Selector.p11AndP37FrobeniusDefectsDiffer

coarseFrobeniusPairDefectSeparates11And43 :
  p11CoarseFrobeniusPairDefect ≡ p43CoarseFrobeniusPairDefect → ⊥
coarseFrobeniusPairDefectSeparates11And43 ()

------------------------------------------------------------------------
-- Consume the actual geometric realization witnesses for both non-Ogg controls.
------------------------------------------------------------------------

p37IndependentGeometricRealization :
  Spectrum.SupersingularFrobeniusNormalFormRealization
    Matrix.prime37 P37Geo.p37FrobeniusCarrier
p37IndependentGeometricRealization = P37Geo.p37GeometricSpectrumRealization

p43IndependentGeometricRealization :
  Spectrum.SupersingularFrobeniusNormalFormRealization
    Matrix.prime43 P43Geo.p43FrobeniusCarrier
p43IndependentGeometricRealization = P43Geo.p43GeometricSpectrumRealization

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
    independentP37GeometricRealization : Bool
    independentP43GeometricRealization : Bool
    p43NontrivialStabilizerControlDefectOne : Bool
    finiteUnder72ZeroDefectMatchesOgg : Bool
    finiteScanIsIndependentGeometricAllPrimeProof : Bool
    secondIndependentControlGeometryStillMissing : Bool

canonicalP11P37MarkedDeckSelectorCutsetBoundary :
  P11P37MarkedDeckSelectorCutsetBoundary
canonicalP11P37MarkedDeckSelectorCutsetBoundary = record
  { p11ScalarHeckeFrobeniusNeedsDeckRefinement = true
  ; p37ScalarHeckeFrobeniusNeedsDeckRefinement = true
  ; deckRefinementIsThereforeOggSelector = false
  ; coarseFrobeniusPairDefectSeparates11And37 = true
  ; independentP37GeometricRealization = true
  ; independentP43GeometricRealization = true
  ; p43NontrivialStabilizerControlDefectOne = true
  ; finiteUnder72ZeroDefectMatchesOgg = true
  ; finiteScanIsIndependentGeometricAllPrimeProof = false
  ; secondIndependentControlGeometryStillMissing = false
  }
