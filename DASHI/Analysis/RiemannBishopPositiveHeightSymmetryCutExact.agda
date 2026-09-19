module DASHI.Analysis.RiemannBishopPositiveHeightSymmetryCutExact where

------------------------------------------------------------------------
-- POSITIVE-HEIGHT PT AUTHORITY -> SYMMETRIC LOCATED LOW REGION
--
-- The published verification is naturally stated for positive ordinates.
-- On Bishop reals, apartness from zero is definitionally the constructive sign
-- split t < 0 or 0 < t.  Thus the symmetric absolute-height low theorem needs
-- exactly:
--
--   1. nontrivial zeros have signed ordinate apart from zero;
--   2. conjugation preserves the selected nontrivial-zero predicate;
--   3. the positive-ordinate PT theorem on this same completed-zeta substrate;
--   4. concrete conjugation/absolute-value geometry.
--
-- This owner isolates the first three source/analytic obligations.  No
-- excluded-middle sign decision is requested.
------------------------------------------------------------------------

open import Agda.Primitive using (Set; Set₁)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import Real as Bishop

import DASHI.Analysis.RiemannAnalyticSubstrate as Analytic
import DASHI.Analysis.RiemannAristotleUniversalEvenConeBidiExact as Universal
import DASHI.Analysis.RiemannBishopComplexAnalyticCarrierExact as BishopComplex
import DASHI.Analysis.RiemannBishopAnalyticLocatedHeightAttachmentExact as BishopAttachment
import DASHI.Analysis.RiemannAnalyticLocatedHeightCarrierRealizationExact as Located

cast : ∀ {A B : Set} → A ≡ B → A → B
cast refl value = value

signedOrdinate :
  ∀ {analytic functions} →
  (carrier :
    BishopComplex.CanonicalBishopComplexCarrierRealization analytic functions) →
  Universal.AnalyticNontrivialZero analytic →
  Bishop.ℝ
signedOrdinate {analytic} carrier rho =
  cast
    (Located.realCarrierIdentity
      (BishopAttachment.toBishopLocatedHeightAttachment carrier))
    (Analytic.ComplexAnalyticCarrier.imaginaryPart
      (Analytic.AnalyticSubstrate.carrier analytic)
      (Universal.point rho))

record BishopNontrivialZeroOrdinateApartZero
    {analytic : Analytic.AnalyticSubstrate}
    {functions : BishopComplex.BishopComplexAnalyticFunctionLayer}
    (carrier :
      BishopComplex.CanonicalBishopComplexCarrierRealization analytic functions)
    : Set₁ where
  field
    signedOrdinateApartZero :
      (rho : Universal.AnalyticNontrivialZero analytic) →
      Bishop._≄_ (signedOrdinate carrier rho) Bishop.0ℝ

open BishopNontrivialZeroOrdinateApartZero public

record AnalyticConjugateNontrivialZeroSymmetry
    (analytic : Analytic.AnalyticSubstrate) : Set₁ where
  field
    conjugatePreservesNontrivialZero :
      (s : Analytic.ComplexAnalyticCarrier.Complex
        (Analytic.AnalyticSubstrate.carrier analytic)) →
      Analytic.CompletedRiemannZeta.nontrivialZero
        (Analytic.AnalyticSubstrate.completed analytic) s →
      Analytic.CompletedRiemannZeta.nontrivialZero
        (Analytic.AnalyticSubstrate.completed analytic)
        (Analytic.ComplexAnalyticCarrier.conjC
          (Analytic.AnalyticSubstrate.carrier analytic) s)

open AnalyticConjugateNontrivialZeroSymmetry public

record PositiveOrdinatePlattTrudgianCriticality
    {analytic : Analytic.AnalyticSubstrate}
    {functions : BishopComplex.BishopComplexAnalyticFunctionLayer}
    (carrier :
      BishopComplex.CanonicalBishopComplexCarrierRealization analytic functions)
    : Set₁ where
  field
    positiveVerifiedZeroCritical :
      (rho : Universal.AnalyticNontrivialZero analytic) →
      Bishop._<_ Bishop.0ℝ (signedOrdinate carrier rho) →
      Located.LocatedVerifiedRegion
        (BishopAttachment.toBishopLocatedHeightAttachment carrier)
        rho →
      Universal.analyticCritical rho

open PositiveOrdinatePlattTrudgianCriticality public

record BishopPositiveHeightSymmetryCutBoundary : Set where
  constructor bishop-positive-height-symmetry-cut-boundary
  field
    classicalSignDecisionRequired : Bool
    nonzeroSignedOrdinateTheoremRequired : Bool
    conjugateNontrivialZeroTheoremRequired : Bool
    positivePublishedTheoremRequired : Bool
    absoluteLowTheoremPrimitiveRequired : Bool
    rhDerivedHere : Bool

open BishopPositiveHeightSymmetryCutBoundary public

canonicalBishopPositiveHeightSymmetryCutBoundary :
  BishopPositiveHeightSymmetryCutBoundary
canonicalBishopPositiveHeightSymmetryCutBoundary =
  bishop-positive-height-symmetry-cut-boundary
    false true true true false false
