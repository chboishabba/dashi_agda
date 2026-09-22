module DASHI.Moonshine.EisensteinBishopLegacyCoordinateTransportExact where

------------------------------------------------------------------------
-- BISHOP ADDITIVE SERIES -> LEGACY CONCRETE-COMPLEX COORDINATE LIMITS
--
-- The concrete Murray--Bishop real backend is setoid-based, while the older
-- ConcreteComplex carrier sits over ConstructedOrderedCompleteReal with
-- propositional equality.  They are NOT identified definitionally here.
--
-- Instead this module reuses the existing explicit BishopLegacySeriesTransport
-- and pays two purely structural seams:
--
--   1. projection of a finite complex sum is the corresponding finite real sum;
--   2. a transported Bishop series convergence can be exposed through the
--      selected Nat-function sequential-limit algebra.
--
-- Four Bishop source series plus pointwise term-identification witnesses then
-- construct E4E6AdditiveCoordinateSeriesLimits.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans)

import Real as BishopReal
import Sequence as BishopSequence

import DASHI.Analysis.ConstructiveRealSpine as LegacyReal
import DASHI.Analysis.ConstructiveSeries as LegacySeries
import DASHI.Analysis.ConcreteComplex as Complex
import DASHI.Analysis.BishopConstructiveSeriesAdapterExact as BishopAdapter
import DASHI.Foundations.BishopEventualAbsoluteComparisonExact as Comparison
import DASHI.Moonshine.JInvariantEisensteinFiniteQSeriesExact as Finite
import DASHI.Moonshine.EisensteinTruncationSeriesAlignmentExact as Alignment
import DASHI.Moonshine.EisensteinComponentwiseComplexLimitExact as Component

private
  RealCarrier :
    (C : Complex.ConstructedComplexPackage) → Set
  RealCarrier C =
    LegacyReal.Real (LegacyReal.real (Complex.realPackage C))

  ComplexCarrier :
    (C : Complex.ConstructedComplexPackage) → Set
  ComplexCarrier C =
    Complex.ComplexPair (LegacyReal.real (Complex.realPackage C))

------------------------------------------------------------------------
-- 1. Complex finite sums project to the legacy real finite-sum owner.
------------------------------------------------------------------------

realProjectionFiniteSum :
  ∀ {C}
    (term : Nat → ComplexCarrier C)
    (n : Nat) →
  Complex.re (Alignment.complexFiniteSumThrough term n)
  ≡
  LegacySeries.finiteSumThrough
    (LegacyReal.real (Complex.realPackage C))
    (λ index → Complex.re (term index))
    n
realProjectionFiniteSum term zero = refl
realProjectionFiniteSum {C} term (suc n) =
  cong
    (λ old →
      LegacyReal._+_
        (LegacyReal.real (Complex.realPackage C))
        old
        (Complex.re (term (suc n))))
    (realProjectionFiniteSum term n)

imagProjectionFiniteSum :
  ∀ {C}
    (term : Nat → ComplexCarrier C)
    (n : Nat) →
  Complex.im (Alignment.complexFiniteSumThrough term n)
  ≡
  LegacySeries.finiteSumThrough
    (LegacyReal.real (Complex.realPackage C))
    (λ index → Complex.im (term index))
    n
imagProjectionFiniteSum term zero = refl
imagProjectionFiniteSum {C} term (suc n) =
  cong
    (λ old →
      LegacyReal._+_
        (LegacyReal.real (Complex.realPackage C))
        old
        (Complex.im (term (suc n))))
    (imagProjectionFiniteSum term n)

------------------------------------------------------------------------
-- 2. Explicit bridge from legacy admitted sequences to Nat-function limits.
------------------------------------------------------------------------

record LegacyFunctionSeriesLimitBridge
    (C : Complex.ConstructedComplexPackage)
    (S :
      LegacySeries.FunctionSequenceRealization
        (LegacyReal.real (Complex.realPackage C)))
    (L : Component.RealSequentialLimitAlgebra C) : Set₁ where
  field
    transportedSeriesConvergenceToFunctionLimit :
      ∀ {term limit} →
      LegacyReal.ConvergesTo
        (LegacyReal.real (Complex.realPackage C))
        (LegacySeries.seriesPartialSums S term)
        limit →
      Component.ConvergesTo L
        (LegacySeries.partialSumFunction
          (LegacyReal.real (Complex.realPackage C))
          term)
        limit

open LegacyFunctionSeriesLimitBridge public

------------------------------------------------------------------------
-- 3. One Bishop source series transported to one legacy target term family.
------------------------------------------------------------------------

record BishopToLegacyCoordinateSeries
    (C : Complex.ConstructedComplexPackage)
    (S :
      LegacySeries.FunctionSequenceRealization
        (LegacyReal.real (Complex.realPackage C)))
    (transport :
      BishopAdapter.BishopLegacySeriesTransport
        (LegacyReal.real (Complex.realPackage C))
        S)
    (targetTerm : Nat → RealCarrier C) : Set₁ where
  field
    bishopTerm : Nat → BishopReal.ℝ

    bishopLimit : BishopReal.ℝ

    bishopConverges :
      BishopSequence._ConvergesTo_
        (BishopSequence.SeriesOf bishopTerm)
        bishopLimit

    transportedTermMatchesTarget :
      (n : Nat) →
      BishopAdapter.termsToLegacy transport bishopTerm n
      ≡ targetTerm n

open BishopToLegacyCoordinateSeries public

transportedTargetLimit :
  ∀ {C S L transport targetTerm} →
  (bridge : LegacyFunctionSeriesLimitBridge C S L) →
  (series :
    BishopToLegacyCoordinateSeries C S transport targetTerm) →
  Component.ConvergesTo L
    (LegacySeries.partialSumFunction
      (LegacyReal.real (Complex.realPackage C))
      targetTerm)
    (BishopAdapter.toLegacy transport
      (bishopLimit series))
transportedTargetLimit {C} {S} {L} {transport} {targetTerm} bridge series =
  Component.pointwiseLimitTransport L
    partialSumsMatch
    (transportedSeriesConvergenceToFunctionLimit bridge
      (BishopAdapter.convergenceTransport transport
        (bishopConverges series)))
  where
  transportedTerm :
    Nat → RealCarrier C
  transportedTerm =
    BishopAdapter.termsToLegacy transport (bishopTerm series)

  partialSumsMatch :
    (n : Nat) →
    LegacySeries.partialSumFunction
      (LegacyReal.real (Complex.realPackage C))
      transportedTerm
      n
    ≡
    LegacySeries.partialSumFunction
      (LegacyReal.real (Complex.realPackage C))
      targetTerm
      n
  partialSumsMatch zero =
    transportedTermMatchesTarget series zero
  partialSumsMatch (suc n) =
    trans
      (cong
        (λ newest →
          LegacyReal._+_
            (LegacyReal.real (Complex.realPackage C))
            (LegacySeries.partialSumFunction
              (LegacyReal.real (Complex.realPackage C))
              transportedTerm n)
            newest)
        (transportedTermMatchesTarget series (suc n)))
      (cong
        (λ old →
          LegacyReal._+_
            (LegacyReal.real (Complex.realPackage C))
            old
            (targetTerm (suc n)))
        (partialSumsMatch n))


------------------------------------------------------------------------
-- 3a. Bishop coordinate convergence can itself be compiled from a majorant.
------------------------------------------------------------------------

record BishopCoordinateMajorantData
    (target : Nat → BishopReal.ℝ) : Set₁ where
  field
    majorant : Nat → BishopReal.ℝ

    eventualAbsoluteMajorant :
      Comparison.EventualAbsoluteMajorant target majorant

open BishopCoordinateMajorantData public

bishopCoordinateConvergenceFromMajorant :
  ∀ {target} →
  BishopCoordinateMajorantData target →
  BishopSequence._isConvergent
    (BishopSequence.SeriesOf target)
bishopCoordinateConvergenceFromMajorant data =
  Comparison.eventualAbsoluteComparisonConverges
    (eventualAbsoluteMajorant data)

bishopCoordinateLimitFromMajorant :
  ∀ {target} →
  BishopCoordinateMajorantData target →
  BishopReal.ℝ
bishopCoordinateLimitFromMajorant data =
  BishopSequence.lim
    (bishopCoordinateConvergenceFromMajorant data)

bishopCoordinateConvergesToMajorantLimit :
  ∀ {target} →
  (data : BishopCoordinateMajorantData target) →
  BishopSequence._ConvergesTo_
    (BishopSequence.SeriesOf target)
    (bishopCoordinateLimitFromMajorant data)
bishopCoordinateConvergesToMajorantLimit data =
  Data.Product.Base.proj₂
    (bishopCoordinateConvergenceFromMajorant data)

bishopCoordinateSeriesFromMajorant :
  ∀ {C S transport targetTerm} →
  (bishopTarget : Nat → BishopReal.ℝ) →
  (majorant : BishopCoordinateMajorantData bishopTarget) →
  ((n : Nat) →
    BishopAdapter.termsToLegacy transport bishopTarget n
    ≡ targetTerm n) →
  BishopToLegacyCoordinateSeries C S transport targetTerm
bishopCoordinateSeriesFromMajorant bishopTarget majorant termMatch =
  record
    { bishopTerm = bishopTarget
    ; bishopLimit = bishopCoordinateLimitFromMajorant majorant
    ; bishopConverges =
        bishopCoordinateConvergesToMajorantLimit majorant
    ; transportedTermMatchesTarget = termMatch
    }

------------------------------------------------------------------------
-- 4. Four coordinate transports for E4/E6.
------------------------------------------------------------------------

record E4E6BishopCoordinateTransport
    (C : Complex.ConstructedComplexPackage)
    (S :
      LegacySeries.FunctionSequenceRealization
        (LegacyReal.real (Complex.realPackage C)))
    (transport :
      BishopAdapter.BishopLegacySeriesTransport
        (LegacyReal.real (Complex.realPackage C))
        S)
    (kernel : Finite.DivisorPowerKernel)
    (tau : ComplexCarrier C) : Set₁ where
  field
    e4Real :
      BishopToLegacyCoordinateSeries
        C S transport
        (λ n → Complex.re
          (Alignment.e4SeriesTerm C kernel tau n))

    e4Imag :
      BishopToLegacyCoordinateSeries
        C S transport
        (λ n → Complex.im
          (Alignment.e4SeriesTerm C kernel tau n))

    e6Real :
      BishopToLegacyCoordinateSeries
        C S transport
        (λ n → Complex.re
          (Alignment.e6SeriesTerm C kernel tau n))

    e6Imag :
      BishopToLegacyCoordinateSeries
        C S transport
        (λ n → Complex.im
          (Alignment.e6SeriesTerm C kernel tau n))

open E4E6BishopCoordinateTransport public

compileBishopCoordinateTransport :
  ∀ {C S L transport kernel tau} →
  (bridge : LegacyFunctionSeriesLimitBridge C S L) →
  E4E6BishopCoordinateTransport
    C S transport kernel tau →
  Component.E4E6AdditiveCoordinateSeriesLimits
    C L kernel tau
compileBishopCoordinateTransport
    {C} {S} {L} {transport} {kernel} {tau}
    bridge inputs =
  record
    { Component.e4SeriesLimit =
        Complex.complex
          (BishopAdapter.toLegacy transport
            (bishopLimit (e4Real inputs)))
          (BishopAdapter.toLegacy transport
            (bishopLimit (e4Imag inputs)))
    ; Component.e6SeriesLimit =
        Complex.complex
          (BishopAdapter.toLegacy transport
            (bishopLimit (e6Real inputs)))
          (BishopAdapter.toLegacy transport
            (bishopLimit (e6Imag inputs)))

    ; Component.e4SeriesRealConverges =
        Component.pointwiseLimitTransport L
          (λ n →
            sym
              (realProjectionFiniteSum
                (Alignment.e4SeriesTerm C kernel tau) n))
          (transportedTargetLimit bridge (e4Real inputs))

    ; Component.e4SeriesImagConverges =
        Component.pointwiseLimitTransport L
          (λ n →
            sym
              (imagProjectionFiniteSum
                (Alignment.e4SeriesTerm C kernel tau) n))
          (transportedTargetLimit bridge (e4Imag inputs))

    ; Component.e6SeriesRealConverges =
        Component.pointwiseLimitTransport L
          (λ n →
            sym
              (realProjectionFiniteSum
                (Alignment.e6SeriesTerm C kernel tau) n))
          (transportedTargetLimit bridge (e6Real inputs))

    ; Component.e6SeriesImagConverges =
        Component.pointwiseLimitTransport L
          (λ n →
            sym
              (imagProjectionFiniteSum
                (Alignment.e6SeriesTerm C kernel tau) n))
          (transportedTargetLimit bridge (e6Imag inputs))
    }

------------------------------------------------------------------------
-- 5. Frontier.
------------------------------------------------------------------------

record EisensteinBishopLegacyCoordinateBoundary : Set where
  constructor eisenstein-bishop-legacy-coordinate-boundary
  field
    complexFiniteSumProjectionPaid : Bool
    bishopLegacyCarrierIdentificationAvoided : Bool
    ordinaryBishopSeriesConvergenceTransportedExplicitly : Bool
    bishopCoordinateConvergenceCompilesFromMajorant : Bool
    fourCoordinateTransportCompilesAdditiveLimits : Bool

    concreteBishopCoordinateTermIdentificationsInhabited : Bool
    legacyFunctionSeriesLimitBridgeInhabited : Bool

open import Agda.Builtin.Bool using (Bool; true; false)
open EisensteinBishopLegacyCoordinateBoundary public

canonicalEisensteinBishopLegacyCoordinateBoundary :
  EisensteinBishopLegacyCoordinateBoundary
canonicalEisensteinBishopLegacyCoordinateBoundary =
  eisenstein-bishop-legacy-coordinate-boundary
    true true true true true
    false false
