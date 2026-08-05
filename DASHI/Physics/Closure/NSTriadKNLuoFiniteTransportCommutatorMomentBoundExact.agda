module DASHI.Physics.Closure.NSTriadKNLuoFiniteTransportCommutatorMomentBoundExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Authors: Tosio Kato; Gustavo Ponce.
-- Title: "Commutator Estimates and the Euler and Navier--Stokes Equations".
-- Communications on Pure and Applied Mathematics 41 (1988), 891--907.
-- DOI: 10.1002/cpa.3160410704.
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- Springer, 2011.
-- DOI: 10.1007/978-3-642-16830-7.
--
-- PURPOSE
-- Turn the exact finite transport-commutator identity into its first-moment
-- majorant.  Pointwise assumptions
--
--   |a(y)-a(0)| <= |y| A,
--   |g(y)| <= G
--
-- imply
--
--   sum_y w_y |a(y)-a(0)| |g(y)|
--     <= A G sum_y w_y |y|.
--
-- All quantities are explicit nonnegative rational magnitudes.  This is the
-- finite ordered core of the Littlewood--Paley commutator estimate; the
-- continuum producer must identify the samples with an actual kernel and
-- prove the moment scaling.
------------------------------------------------------------------------

open import Agda.Builtin.List using (List)
open import Data.Rational.Base using
  (ℚ; 0ℚ; _*_; _≤_; nonNegative)
import Data.Rational.Properties as ℚₚ
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst)

import DASHI.Physics.Closure.NSTriadKNLuoFiniteCenteredCommutatorBudgetExact as Sum

record TransportMomentSample : Set where
  constructor transport-moment-sample
  field
    weight displacementMagnitude : ℚ
    transportIncrementMagnitude derivativeMagnitude : ℚ
    weightNonnegative : 0ℚ ≤ weight
    displacementNonnegative : 0ℚ ≤ displacementMagnitude
    incrementNonnegative : 0ℚ ≤ transportIncrementMagnitude
    derivativeNonnegative : 0ℚ ≤ derivativeMagnitude

open TransportMomentSample public

weightedCommutatorMagnitude : TransportMomentSample → ℚ
weightedCommutatorMagnitude sample =
  weight sample
  * (transportIncrementMagnitude sample * derivativeMagnitude sample)

weightedFirstMoment : TransportMomentSample → ℚ
weightedFirstMoment sample =
  weight sample * displacementMagnitude sample

record TransportCommutatorMomentBudget : Set₁ where
  field
    samples : List TransportMomentSample
    transportGradient derivativeEnvelope : ℚ
    transportGradientNonnegative : 0ℚ ≤ transportGradient
    derivativeEnvelopeNonnegative : 0ℚ ≤ derivativeEnvelope
    incrementBound :
      (sample : TransportMomentSample) →
      transportIncrementMagnitude sample
      ≤ displacementMagnitude sample * transportGradient
    derivativeBound :
      (sample : TransportMomentSample) →
      derivativeMagnitude sample ≤ derivativeEnvelope

open TransportCommutatorMomentBudget public

pointwiseFirstMomentBound :
  (budget : TransportCommutatorMomentBudget) →
  (sample : TransportMomentSample) →
  weightedCommutatorMagnitude sample
  ≤ transportGradient budget
      * derivativeEnvelope budget
      * weightedFirstMoment sample
pointwiseFirstMomentBound budget sample =
  let
    incrementTimesDerivative :
      transportIncrementMagnitude sample * derivativeMagnitude sample
      ≤ (displacementMagnitude sample * transportGradient budget)
          * derivativeMagnitude sample
    incrementTimesDerivative =
      let
        instance
          derivativeIsNonnegative =
            nonNegative (derivativeNonnegative sample)
      in
      ℚₚ.*-monoʳ-≤-nonNeg
        (derivativeMagnitude sample)
        (incrementBound budget sample)

    displacementTimesGradientNonnegative :
      0ℚ ≤ displacementMagnitude sample * transportGradient budget
    displacementTimesGradientNonnegative =
      let
        instance
          displacementIsNonnegative =
            nonNegative (displacementNonnegative sample)
          gradientIsNonnegative =
            nonNegative (transportGradientNonnegative budget)
          productIsNonnegative =
            ℚₚ.nonNeg*nonNeg⇒nonNeg
              (displacementMagnitude sample)
              (transportGradient budget)
      in
      ℚₚ.nonNegative⁻¹
        (displacementMagnitude sample * transportGradient budget)

    replaceDerivative :
      (displacementMagnitude sample * transportGradient budget)
        * derivativeMagnitude sample
      ≤ (displacementMagnitude sample * transportGradient budget)
        * derivativeEnvelope budget
    replaceDerivative =
      let
        instance
          coefficientIsNonnegative =
            nonNegative displacementTimesGradientNonnegative
      in
      ℚₚ.*-monoˡ-≤-nonNeg
        (displacementMagnitude sample * transportGradient budget)
        (derivativeBound budget sample)

    innerBound :
      transportIncrementMagnitude sample * derivativeMagnitude sample
      ≤ (displacementMagnitude sample * transportGradient budget)
        * derivativeEnvelope budget
    innerBound = ℚₚ.≤-trans incrementTimesDerivative replaceDerivative

    weightedBound :
      weight sample
        * (transportIncrementMagnitude sample * derivativeMagnitude sample)
      ≤ weight sample
        * ((displacementMagnitude sample * transportGradient budget)
          * derivativeEnvelope budget)
    weightedBound =
      let
        instance
          weightIsNonnegative = nonNegative (weightNonnegative sample)
      in
      ℚₚ.*-monoˡ-≤-nonNeg (weight sample) innerBound

    targetMeaning :
      weight sample
        * ((displacementMagnitude sample * transportGradient budget)
          * derivativeEnvelope budget)
      ≡ transportGradient budget
          * derivativeEnvelope budget
          * weightedFirstMoment sample
    targetMeaning =
      solve
        ( weight sample
        ∷ displacementMagnitude sample
        ∷ transportGradient budget
        ∷ derivativeEnvelope budget
        ∷ [])
  in
  subst
    (λ upper → weightedCommutatorMagnitude sample ≤ upper)
    targetMeaning
    weightedBound

finiteTransportCommutatorFirstMomentBound :
  (budget : TransportCommutatorMomentBudget) →
  Sum.sumBy (samples budget) weightedCommutatorMagnitude
  ≤ transportGradient budget
      * derivativeEnvelope budget
      * Sum.sumBy (samples budget) weightedFirstMoment
finiteTransportCommutatorFirstMomentBound budget =
  let
    coefficient =
      transportGradient budget * derivativeEnvelope budget

    pointwiseSum :
      Sum.sumBy (samples budget) weightedCommutatorMagnitude
      ≤ Sum.sumBy (samples budget)
          (λ sample → coefficient * weightedFirstMoment sample)
    pointwiseSum =
      Sum.sumByMonotone
        (samples budget)
        weightedCommutatorMagnitude
        (λ sample → coefficient * weightedFirstMoment sample)
        (pointwiseFirstMomentBound budget)

    factorMeaning :
      Sum.sumBy (samples budget)
        (λ sample → coefficient * weightedFirstMoment sample)
      ≡ coefficient * Sum.sumBy (samples budget) weightedFirstMoment
    factorMeaning =
      Sum.sumByScaleLeft
        coefficient
        (samples budget)
        weightedFirstMoment
  in
  subst
    (λ upper →
      Sum.sumBy (samples budget) weightedCommutatorMagnitude ≤ upper)
    factorMeaning
    pointwiseSum
