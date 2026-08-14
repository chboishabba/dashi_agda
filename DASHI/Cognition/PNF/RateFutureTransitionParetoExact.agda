module DASHI.Cognition.PNF.RateFutureTransitionParetoExact where

------------------------------------------------------------------------
-- QUOTIENT + RATE + GEOMETRY
--
-- Future rate-distortion fixes which candidates are admissible and how cheaply
-- they encode.  It need not select a unique dynamical geometry.  This module
-- makes the second optimization explicit: among minimum-rate feasible codes,
-- minimize transition cost (and, separately, reopening cost).
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Rational.Base using (ℚ; 0ℚ; _≤_)

import DASHI.Cognition.PNF.FutureRateDistortionGenericExact as RD
import DASHI.Cognition.PNF.OrientedZeroGrayTransitionGeometryExact as Wave

record RepresentationGeometryFamily : Set₁ where
  constructor representationGeometryFamily
  field
    Candidate : Set
    rate : Candidate → Nat
    futureDistortion : Candidate → ℚ
    transitionCost : Candidate → Nat
    reopenCost : Candidate → Nat

open RepresentationGeometryFamily public

FutureFeasible : RepresentationGeometryFamily → ℚ → Set → Set
FutureFeasible family epsilon _ = ⊤

record RateOptimalAt
    (family : RepresentationGeometryFamily)
    (epsilon : ℚ)
    (selected : Candidate family) : Set₁ where
  field
    selectedFutureFeasible : futureDistortion family selected ≤ epsilon
    minimumRate :
      (candidate : Candidate family) →
      futureDistortion family candidate ≤ epsilon →
      rate family selected ≤ rate family candidate

open RateOptimalAt public

record TransitionOptimalAmongRateOptimal
    (family : RepresentationGeometryFamily)
    (epsilon : ℚ)
    (selected : Candidate family) : Set₁ where
  field
    selectedRateOptimal : RateOptimalAt family epsilon selected
    minimumTransitionAtSameRate :
      (candidate : Candidate family) →
      futureDistortion family candidate ≤ epsilon →
      rate family candidate ≡ rate family selected →
      transitionCost family selected ≤ transitionCost family candidate

open TransitionOptimalAmongRateOptimal public

record ReopenOptimalAmongRateAndTransitionOptimal
    (family : RepresentationGeometryFamily)
    (epsilon : ℚ)
    (selected : Candidate family) : Set₁ where
  field
    selectedTransitionOptimal :
      TransitionOptimalAmongRateOptimal family epsilon selected
    minimumReopenAtSameRateAndTransition :
      (candidate : Candidate family) →
      futureDistortion family candidate ≤ epsilon →
      rate family candidate ≡ rate family selected →
      transitionCost family candidate ≡ transitionCost family selected →
      reopenCost family selected ≤ reopenCost family candidate

open ReopenOptimalAmongRateAndTransitionOptimal public

------------------------------------------------------------------------
-- Forgetting the geometric coordinates recovers the existing rate-distortion
-- family exactly.
------------------------------------------------------------------------

toRateDistortionFamily : RepresentationGeometryFamily → RD.RateDistortionFamily
toRateDistortionFamily family =
  RD.rateDistortionFamily
    (Candidate family)
    (rate family)
    (futureDistortion family)

rateOptimalGivesRateDistortionOptimal :
  ∀ {family epsilon selected} →
  RateOptimalAt family epsilon selected →
  RD.OptimalAt (toRateDistortionFamily family) epsilon
rateOptimalGivesRateDistortionOptimal optimum =
  RD.optimalAt
    _
    (selectedFutureFeasible optimum)
    (minimumRate optimum)

------------------------------------------------------------------------
-- Concrete Wave4 regression: ordinary binary and Gray have equal exact rate
-- and zero future distortion, yet Gray has smaller transition cost.  Thus the
-- first optimization cannot determine the second.
------------------------------------------------------------------------

data WaveCode : Set where ordinaryBinary gray : WaveCode

waveRate : WaveCode → Nat
waveRate ordinaryBinary = 2
waveRate gray = 2

waveFutureDistortion : WaveCode → ℚ
waveFutureDistortion ordinaryBinary = 0ℚ
waveFutureDistortion gray = 0ℚ

waveTransitionCost : WaveCode → Nat
waveTransitionCost ordinaryBinary = Wave.binaryPathDistortion
waveTransitionCost gray = Wave.grayPathDistortion

waveReopenCost : WaveCode → Nat
waveReopenCost ordinaryBinary = 0
waveReopenCost gray = 0

waveFamily : RepresentationGeometryFamily
waveFamily = representationGeometryFamily
  WaveCode waveRate waveFutureDistortion waveTransitionCost waveReopenCost

waveBinaryAndGrayHaveSameRate : waveRate ordinaryBinary ≡ waveRate gray
waveBinaryAndGrayHaveSameRate = refl

waveBinaryAndGrayAreExact :
  waveFutureDistortion ordinaryBinary ≡ 0ℚ
  × waveFutureDistortion gray ≡ 0ℚ
waveBinaryAndGrayAreExact = refl , refl

waveGrayStrictlyImprovesTransition :
  waveTransitionCost gray < waveTransitionCost ordinaryBinary
waveGrayStrictlyImprovesTransition = Wave.grayStrictlyImprovesPathDistortion

waveGrayRateOptimalAtZero : RateOptimalAt waveFamily 0ℚ gray
waveGrayRateOptimalAtZero = record
  { selectedFutureFeasible = ≤-refl
  ; minimumRate = minimum
  }
  where
    minimum : (candidate : WaveCode) →
      waveFutureDistortion candidate ≤ 0ℚ → 2 ≤ waveRate candidate
    minimum ordinaryBinary feasible = ≤-refl
    minimum gray feasible = ≤-refl

waveGrayTransitionOptimalAtZero :
  TransitionOptimalAmongRateOptimal waveFamily 0ℚ gray
waveGrayTransitionOptimalAtZero = record
  { selectedRateOptimal = waveGrayRateOptimalAtZero
  ; minimumTransitionAtSameRate = minimum
  }
  where
    minimum : (candidate : WaveCode) →
      waveFutureDistortion candidate ≤ 0ℚ →
      waveRate candidate ≡ waveRate gray →
      waveTransitionCost gray ≤ waveTransitionCost candidate
    minimum ordinaryBinary feasible sameRate =
      Wave.waveGrayOptimalAgainstBinary
    minimum gray feasible sameRate = ≤-refl

------------------------------------------------------------------------
-- The theorem surface therefore implements the nested optimization proposed by
-- the representation-geometry programme:
--
--   semantic stage:  minimize rate subject to future distortion <= epsilon;
--   geometric stage: minimize transition cost among those rate optima;
--   operational stage: optionally minimize reopen cost among ties.
------------------------------------------------------------------------
