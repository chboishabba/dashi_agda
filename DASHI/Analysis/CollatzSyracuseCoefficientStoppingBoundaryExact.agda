module DASHI.Analysis.CollatzSyracuseCoefficientStoppingBoundaryExact where

------------------------------------------------------------------------
-- COEFFICIENT STOPPING VS LITERAL STOPPING
--
-- This is the exact same-object seam behind the historical coefficient
-- stopping route.  For one literal Syracuse start x:
--
--   coefficient-contracting at m : 3^(s_m(x)) < 2^m
--   literal descent at m          : T^m(x) < x.
--
-- Literal descent always implies coefficient contraction at the same horizon,
-- because the affine correction is nonnegative.  Therefore the first
-- coefficient-contracting horizon is no later than the first literal descent
-- horizon.
--
-- Equality follows if the affine correction already fits inside the positive
-- coefficient gap at the first contracting horizon.  The universal assertion
-- that this always happens is intentionally NOT inhabited here: it is the
-- historical coefficient-stopping equality route, and external literature is
-- attribution/context rather than Agda proof authority.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _*_)
open import Data.Empty using (⊥-elim)
open import Data.Nat using (_≤_; _<_)
import Data.Nat.Properties as NatP
open import Relation.Binary.Definitions using (tri<; tri≈; tri>)
open import Relation.Binary.PropositionalEquality using (subst; sym)
open import Relation.Nullary using (¬_)

import DASHI.NumberTheory.Collatz.SyracuseExact as Syracuse
import DASHI.NumberTheory.Collatz.SyracuseParityItineraryExact as Itinerary
import DASHI.NumberTheory.Collatz.SyracuseAffineIterateExact as Affine
import DASHI.Analysis.CollatzSyracuseExactAffineTerminalExact as Terminal
import DASHI.Analysis.CollatzSyracuseParadoxicalPrefixExact as Paradox

CoefficientContractsAt : Syracuse.PositiveNat → Nat → Set
CoefficientContractsAt x m =
  Affine.powNat 3
    (Affine.parityCount (Itinerary.parityWord m x))
  < Affine.powNat 2 m

LiteralDescendsAt : Syracuse.PositiveNat → Nat → Set
LiteralDescendsAt x m =
  Syracuse.toNat (Syracuse.syracuseIterate m x) < Syracuse.toNat x

contractingGapImpliesCoefficientContracts :
  {x : Syracuse.PositiveNat} {m : Nat} →
  Paradox.ContractingCoefficientGap (Itinerary.parityWord m x) →
  CoefficientContractsAt x m
contractingGapImpliesCoefficientContracts {x} {m} coefficient =
  let
    multiplier =
      Affine.powNat 3
        (Affine.parityCount (Itinerary.parityWord m x))
    positiveGap = Paradox.gapPositive coefficient

    multiplierBelowSplit :
      multiplier < multiplier + Paradox.gap coefficient
    multiplierBelowSplit = NatP.m<m+n multiplier positiveGap
  in
  subst
    (λ right → multiplier < right)
    (sym (Paradox.denominatorSplit coefficient))
    multiplierBelowSplit

descentImpliesCoefficientContracts :
  (m : Nat) →
  (x : Syracuse.PositiveNat) →
  LiteralDescendsAt x m →
  CoefficientContractsAt x m
descentImpliesCoefficientContracts m (Syracuse.positiveNat n) descent =
  let
    xValue = Syracuse.toNat (Syracuse.positiveNat n)
    multiplier =
      Affine.powNat 3
        (Affine.parityCount
          (Itinerary.parityWord m (Syracuse.positiveNat n)))
    denominator = Affine.powNat 2 m
    correction =
      Affine.affineAdditiveTerm
        (Itinerary.parityWord m (Syracuse.positiveNat n))

    margin :
      multiplier * xValue + correction
      < denominator * xValue
    margin =
      Terminal.strictDescentImpliesExactAffineMargin
        m (Syracuse.positiveNat n) descent

    multiplierProductBelowNumerator :
      multiplier * xValue
      ≤ multiplier * xValue + correction
    multiplierProductBelowNumerator =
      NatP.m≤m+n (multiplier * xValue) correction

    multiplierProductBelow :
      multiplier * xValue < denominator * xValue
    multiplierProductBelow =
      NatP.≤-<-trans multiplierProductBelowNumerator margin
  in
  NatP.*-cancelʳ-<
    multiplier denominator xValue multiplierProductBelow

record FirstCoefficientContracting
    (x : Syracuse.PositiveNat)
    (m : Nat) : Set where
  field
    coefficientGap :
      Paradox.ContractingCoefficientGap (Itinerary.parityWord m x)
    noEarlierCoefficientContraction :
      (j : Nat) →
      j < m →
      ¬ CoefficientContractsAt x j

open FirstCoefficientContracting public

record FirstLiteralDescent
    (x : Syracuse.PositiveNat)
    (m : Nat) : Set where
  field
    descentAtHorizon : LiteralDescendsAt x m
    noEarlierLiteralDescent :
      (j : Nat) →
      j < m →
      ¬ LiteralDescendsAt x j

open FirstLiteralDescent public

coefficientHorizonAtMostDescentHorizon :
  {x : Syracuse.PositiveNat} {coefficientHorizon descentHorizon : Nat} →
  FirstCoefficientContracting x coefficientHorizon →
  FirstLiteralDescent x descentHorizon →
  coefficientHorizon ≤ descentHorizon
coefficientHorizonAtMostDescentHorizon
  {x} {coefficientHorizon} {descentHorizon}
  coefficientStop literalStop
  with NatP.<-cmp coefficientHorizon descentHorizon
... | tri< coefficientBelow _ _ = NatP.<⇒≤ coefficientBelow
... | tri≈ _ equal _ = NatP.≤-reflexive equal
... | tri> _ _ descentBelow =
  ⊥-elim
    (noEarlierCoefficientContraction coefficientStop
      descentHorizon
      descentBelow
      (descentImpliesCoefficientContracts
        descentHorizon x (descentAtHorizon literalStop)))

literalHorizonAtMostAnyDescent :
  {x : Syracuse.PositiveNat} {literalHorizon candidate : Nat} →
  FirstLiteralDescent x literalHorizon →
  LiteralDescendsAt x candidate →
  literalHorizon ≤ candidate
literalHorizonAtMostAnyDescent
  {x} {literalHorizon} {candidate}
  literalStop candidateDescent
  with NatP.<-cmp literalHorizon candidate
... | tri< literalBelow _ _ = NatP.<⇒≤ literalBelow
... | tri≈ _ equal _ = NatP.≤-reflexive equal
... | tri> _ _ candidateBelow =
  ⊥-elim
    (noEarlierLiteralDescent literalStop
      candidate candidateBelow candidateDescent)

correctionFitAtCoefficientHorizonImpliesEquality :
  {x : Syracuse.PositiveNat} {coefficientHorizon descentHorizon : Nat} →
  (coefficientStop : FirstCoefficientContracting x coefficientHorizon) →
  (literalStop : FirstLiteralDescent x descentHorizon) →
  Affine.affineAdditiveTerm
      (Itinerary.parityWord coefficientHorizon x)
    < Paradox.gap (coefficientGap coefficientStop) * Syracuse.toNat x →
  coefficientHorizon ≡ descentHorizon
correctionFitAtCoefficientHorizonImpliesEquality
  {x} {coefficientHorizon} {descentHorizon}
  coefficientStop literalStop correctionFits =
  let
    descentAtCoefficientHorizon :
      LiteralDescendsAt x coefficientHorizon
    descentAtCoefficientHorizon =
      Paradox.contractingCorrectionFitImpliesLiteralDescent
        (Itinerary.parityWord coefficientHorizon x)
        (coefficientGap coefficientStop)
        x
        correctionFits
        refl

    coefficient≤descent : coefficientHorizon ≤ descentHorizon
    coefficient≤descent =
      coefficientHorizonAtMostDescentHorizon coefficientStop literalStop

    descent≤coefficient : descentHorizon ≤ coefficientHorizon
    descent≤coefficient =
      literalHorizonAtMostAnyDescent
        literalStop descentAtCoefficientHorizon
  in
  NatP.≤-antisym coefficient≤descent descent≤coefficient

------------------------------------------------------------------------
-- Explicit source socket for the historical universal equality route.
------------------------------------------------------------------------

record UniversalCoefficientStoppingEqualitySource : Set₁ where
  field
    equality :
      (x : Syracuse.PositiveNat) →
      1 < Syracuse.toNat x →
      (coefficientHorizon descentHorizon : Nat) →
      FirstCoefficientContracting x coefficientHorizon →
      FirstLiteralDescent x descentHorizon →
      coefficientHorizon ≡ descentHorizon

record CoefficientStoppingBoundary : Set where
  constructor coefficientStoppingBoundary
  field
    literalCoefficientContractingPredicatePaid : Nat
    descentImpliesCoefficientContractionPaid : Nat
    coefficientHorizonAtMostDescentHorizonPaid : Nat
    correctionFitAtCoefficientHorizonImpliesEqualityPaid : Nat
    universalEqualityInterfacePaid : Nat

    universalCoefficientStoppingEqualityPaid : Nat
    externalCSTLiteratureCreatesAgdaProof : Nat
    finiteCSTScanPromotesUniversalEquality : Nat
    semiconvergentClassificationPromotesCorrectionFit : Nat

canonicalCoefficientStoppingBoundary : CoefficientStoppingBoundary
canonicalCoefficientStoppingBoundary =
  coefficientStoppingBoundary
    1 1 1 1 1
    0 0 0 0
