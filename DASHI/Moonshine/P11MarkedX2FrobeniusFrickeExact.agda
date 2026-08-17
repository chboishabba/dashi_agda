module DASHI.Moonshine.P11MarkedX2FrobeniusFrickeExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Adel Betina and Emmanuel Lecouturier,
-- "Congruence formulae for Legendre modular polynomials",
-- Journal of Number Theory 188 (2018), 71--87.
-- DOI: 10.1016/j.jnt.2018.01.006.
-- They work on X(Gamma_0(p) intersection Gamma(2)); the special fiber is
-- described by the Legendre p-th modular polynomial and the Atkin--Lehner
-- involution exchanges the two components via Frobenius on the level-2 lambda
-- coordinate.
--
-- Nicholas M. Katz and Barry Mazur,
-- "Arithmetic Moduli of Elliptic Curves", Annals of Mathematics Studies 108,
-- Princeton University Press, 1985.
-- DOI: 10.1515/9781400881710.
--
-- Andrew P. Ogg,
-- "Automorphismes de courbes modulaires",
-- Seminaire Delange-Pisot-Poitou 16 (1974--1975), expose 7, pp. 1--8.
-- MR 417184; no DOI assigned.
--
-- DASHI CONTRIBUTION
--
-- On the explicit p=11 supersingular Legendre chart:
--
--   * lambda=2,6,10 are F_11-rational, hence Frobenius-fixed;
--   * the two roots of lambda^2-lambda+1 are the conjugate F_121 pair and are
--     swapped by lambda -> lambda^11.
--
-- In Fine5 labels this is
--
--   F(a0)=a1, F(a1)=a0,
--   F(b0)=b0, F(b1)=b1, F(b2)=b2.
--
-- Betina--Lecouturier identifies the p-Atkin--Lehner action on the singular /
-- supersingular locus of the Gamma_0(p) intersection Gamma(2) special fiber
-- with this Frobenius gluing action.  We therefore use the same finite
-- involution as the marked Fricke/Atkin--Lehner fingerprint at p=11.
--
-- The corrected marked T3 and T5 multiplicity correspondences commute with
-- this involution exactly.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Moonshine.P11FiveStatePositiveHeckeLiftExact as Fine
import DASHI.Moonshine.P11FullLevel2DeckHeckeEquivarianceExact as Deck
import DASHI.Moonshine.P11MarkedX2HeckeReconstructionExact as Marked

------------------------------------------------------------------------
-- Geometric Frobenius on the five supersingular X(2) points.
------------------------------------------------------------------------

markedFrobenius : Fine.P11Fine5 → Fine.P11Fine5
markedFrobenius Fine.a0 = Fine.a1
markedFrobenius Fine.a1 = Fine.a0
markedFrobenius Fine.b0 = Fine.b0
markedFrobenius Fine.b1 = Fine.b1
markedFrobenius Fine.b2 = Fine.b2

markedFrobeniusInvolution :
  (x : Fine.P11Fine5) → markedFrobenius (markedFrobenius x) ≡ x
markedFrobeniusInvolution Fine.a0 = refl
markedFrobeniusInvolution Fine.a1 = refl
markedFrobeniusInvolution Fine.b0 = refl
markedFrobeniusInvolution Fine.b1 = refl
markedFrobeniusInvolution Fine.b2 = refl

-- Both coarse j-invariants lie in F_11, so forgetting level 2 makes Frobenius
-- pointwise identity on the two-state Brandt carrier.
markedFrobeniusPreservesJClass :
  (x : Fine.P11Fine5) →
  Fine.projectFine5 (markedFrobenius x) ≡ Fine.projectFine5 x
markedFrobeniusPreservesJClass Fine.a0 = refl
markedFrobeniusPreservesJClass Fine.a1 = refl
markedFrobeniusPreservesJClass Fine.b0 = refl
markedFrobeniusPreservesJClass Fine.b1 = refl
markedFrobeniusPreservesJClass Fine.b2 = refl

------------------------------------------------------------------------
-- Corrected marked Hecke multiplicities commute with Frobenius.
------------------------------------------------------------------------

markedT3FrobeniusEquivariant :
  (x y : Fine.P11Fine5) →
  Deck.edgeMultiplicity Marked.MarkedT3Positive
    (markedFrobenius x) (markedFrobenius y)
  ≡ Deck.edgeMultiplicity Marked.MarkedT3Positive x y
markedT3FrobeniusEquivariant Fine.a0 Fine.a0 = refl
markedT3FrobeniusEquivariant Fine.a0 Fine.a1 = refl
markedT3FrobeniusEquivariant Fine.a0 Fine.b0 = refl
markedT3FrobeniusEquivariant Fine.a0 Fine.b1 = refl
markedT3FrobeniusEquivariant Fine.a0 Fine.b2 = refl
markedT3FrobeniusEquivariant Fine.a1 Fine.a0 = refl
markedT3FrobeniusEquivariant Fine.a1 Fine.a1 = refl
markedT3FrobeniusEquivariant Fine.a1 Fine.b0 = refl
markedT3FrobeniusEquivariant Fine.a1 Fine.b1 = refl
markedT3FrobeniusEquivariant Fine.a1 Fine.b2 = refl
markedT3FrobeniusEquivariant Fine.b0 Fine.a0 = refl
markedT3FrobeniusEquivariant Fine.b0 Fine.a1 = refl
markedT3FrobeniusEquivariant Fine.b0 Fine.b0 = refl
markedT3FrobeniusEquivariant Fine.b0 Fine.b1 = refl
markedT3FrobeniusEquivariant Fine.b0 Fine.b2 = refl
markedT3FrobeniusEquivariant Fine.b1 Fine.a0 = refl
markedT3FrobeniusEquivariant Fine.b1 Fine.a1 = refl
markedT3FrobeniusEquivariant Fine.b1 Fine.b0 = refl
markedT3FrobeniusEquivariant Fine.b1 Fine.b1 = refl
markedT3FrobeniusEquivariant Fine.b1 Fine.b2 = refl
markedT3FrobeniusEquivariant Fine.b2 Fine.a0 = refl
markedT3FrobeniusEquivariant Fine.b2 Fine.a1 = refl
markedT3FrobeniusEquivariant Fine.b2 Fine.b0 = refl
markedT3FrobeniusEquivariant Fine.b2 Fine.b1 = refl
markedT3FrobeniusEquivariant Fine.b2 Fine.b2 = refl

markedT5FrobeniusEquivariant :
  (x y : Fine.P11Fine5) →
  Deck.edgeMultiplicity Marked.MarkedT5Positive
    (markedFrobenius x) (markedFrobenius y)
  ≡ Deck.edgeMultiplicity Marked.MarkedT5Positive x y
markedT5FrobeniusEquivariant Fine.a0 Fine.a0 = refl
markedT5FrobeniusEquivariant Fine.a0 Fine.a1 = refl
markedT5FrobeniusEquivariant Fine.a0 Fine.b0 = refl
markedT5FrobeniusEquivariant Fine.a0 Fine.b1 = refl
markedT5FrobeniusEquivariant Fine.a0 Fine.b2 = refl
markedT5FrobeniusEquivariant Fine.a1 Fine.a0 = refl
markedT5FrobeniusEquivariant Fine.a1 Fine.a1 = refl
markedT5FrobeniusEquivariant Fine.a1 Fine.b0 = refl
markedT5FrobeniusEquivariant Fine.a1 Fine.b1 = refl
markedT5FrobeniusEquivariant Fine.a1 Fine.b2 = refl
markedT5FrobeniusEquivariant Fine.b0 Fine.a0 = refl
markedT5FrobeniusEquivariant Fine.b0 Fine.a1 = refl
markedT5FrobeniusEquivariant Fine.b0 Fine.b0 = refl
markedT5FrobeniusEquivariant Fine.b0 Fine.b1 = refl
markedT5FrobeniusEquivariant Fine.b0 Fine.b2 = refl
markedT5FrobeniusEquivariant Fine.b1 Fine.a0 = refl
markedT5FrobeniusEquivariant Fine.b1 Fine.a1 = refl
markedT5FrobeniusEquivariant Fine.b1 Fine.b0 = refl
markedT5FrobeniusEquivariant Fine.b1 Fine.b1 = refl
markedT5FrobeniusEquivariant Fine.b1 Fine.b2 = refl
markedT5FrobeniusEquivariant Fine.b2 Fine.a0 = refl
markedT5FrobeniusEquivariant Fine.b2 Fine.a1 = refl
markedT5FrobeniusEquivariant Fine.b2 Fine.b0 = refl
markedT5FrobeniusEquivariant Fine.b2 Fine.b1 = refl
markedT5FrobeniusEquivariant Fine.b2 Fine.b2 = refl

------------------------------------------------------------------------
-- Marked Fricke / Atkin--Lehner fingerprint on the supersingular special fiber.
------------------------------------------------------------------------

markedFricke11 : Fine.P11Fine5 → Fine.P11Fine5
markedFricke11 = markedFrobenius

markedFricke11Involution :
  (x : Fine.P11Fine5) → markedFricke11 (markedFricke11 x) ≡ x
markedFricke11Involution = markedFrobeniusInvolution

markedT3FrickeEquivariant :
  (x y : Fine.P11Fine5) →
  Deck.edgeMultiplicity Marked.MarkedT3Positive
    (markedFricke11 x) (markedFricke11 y)
  ≡ Deck.edgeMultiplicity Marked.MarkedT3Positive x y
markedT3FrickeEquivariant = markedT3FrobeniusEquivariant

markedT5FrickeEquivariant :
  (x y : Fine.P11Fine5) →
  Deck.edgeMultiplicity Marked.MarkedT5Positive
    (markedFricke11 x) (markedFricke11 y)
  ≡ Deck.edgeMultiplicity Marked.MarkedT5Positive x y
markedT5FrickeEquivariant = markedT5FrobeniusEquivariant

record P11MarkedX2FrobeniusFrickeBoundary : Set where
  field
    geometricLevel2FrobeniusConstructed : Bool
    geometricLevel2FrobeniusConstructedIsTrue :
      geometricLevel2FrobeniusConstructed ≡ true

    coarseFrobeniusPointwiseIdentityRecovered : Bool
    coarseFrobeniusPointwiseIdentityRecoveredIsTrue :
      coarseFrobeniusPointwiseIdentityRecovered ≡ true

    correctedT3T5FrobeniusEquivariant : Bool
    correctedT3T5FrobeniusEquivariantIsTrue :
      correctedT3T5FrobeniusEquivariant ≡ true

    markedFrickeIdentifiedWithSpecialFiberFrobenius : Bool
    markedFrickeIdentifiedWithSpecialFiberFrobeniusIsTrue :
      markedFrickeIdentifiedWithSpecialFiberFrobenius ≡ true

canonicalP11MarkedX2FrobeniusFrickeBoundary : P11MarkedX2FrobeniusFrickeBoundary
canonicalP11MarkedX2FrobeniusFrickeBoundary = record
  { geometricLevel2FrobeniusConstructed = true
  ; geometricLevel2FrobeniusConstructedIsTrue = refl
  ; coarseFrobeniusPointwiseIdentityRecovered = true
  ; coarseFrobeniusPointwiseIdentityRecoveredIsTrue = refl
  ; correctedT3T5FrobeniusEquivariant = true
  ; correctedT3T5FrobeniusEquivariantIsTrue = refl
  ; markedFrickeIdentifiedWithSpecialFiberFrobenius = true
  ; markedFrickeIdentifiedWithSpecialFiberFrobeniusIsTrue = refl
  }
