module DASHI.Analysis.NonArchimedeanStoppingMomentRepairBidiExact where

------------------------------------------------------------------------
-- STOPPING MOMENT / MGF REPAIR BIDI
--
-- The source documentation promotes the refuted universal survival rate
-- 2^(-t/2) into the MGF domain Re(s) < (1/2) log 2.
--
-- The constructive repair instead gives, for a finite hitting block length m,
--
--   P(T > q m) <= r_m^q,
--   r_m = (2^m - 1) / 2^m = 1 - 2^(-m).
--
-- Hence the correct exponential rate per original time step is
--
--   alpha_m = -(1/m) log r_m.
--
-- Standard geometric-tail probability theory then gives:
--
--   * every polynomial moment E[T^k] is finite;
--   * exponential moments are finite for Re(s) < alpha_m.
--
-- This module records the exact promotion boundary.  It does not claim that
-- Agda kernel-checks real logarithms, infinite sums or the source's probability
-- space.  Those are standard analytic-consumer dependencies.  What is new and
-- repo-owned is the repaired finite geometric tail feeding that consumer.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)


data MomentLeaf : Set where
  finiteHittingBlock : MomentLeaf
  geometricBlockTail : MomentLeaf
  allPolynomialMomentsFinite : MomentLeaf
  repairedExponentialMomentDomain : MomentLeaf
  sourceHalfLogTwoDomain : MomentLeaf


data MomentStatus : Set where
  repoOwned : MomentStatus
  standardConsumer : MomentStatus
  rejected : MomentStatus

momentStatus : MomentLeaf → MomentStatus
momentStatus finiteHittingBlock = repoOwned
momentStatus geometricBlockTail = repoOwned
momentStatus allPolynomialMomentsFinite = standardConsumer
momentStatus repairedExponentialMomentDomain = standardConsumer
momentStatus sourceHalfLogTwoDomain = rejected


data MomentObligation : Set where
  needStandardGeometricTailMomentConsumer : MomentObligation
  rejectedUniversalHalfLogTwoMGFDomain : MomentObligation

polynomialMomentCutset : List MomentObligation
polynomialMomentCutset = needStandardGeometricTailMomentConsumer ∷ []

sourceMGFDomainDisposition : List MomentObligation
sourceMGFDomainDisposition = rejectedUniversalHalfLogTwoMGFDomain ∷ []

record RepairedMomentRateBoundary : Set where
  constructor repairedMomentRateBoundary
  field
    blockTailRatioIsOneMinusTwoToMinusM : Bool
    rateDependsOnHittingBlockLength : Bool
    allPolynomialMomentsFollowFromGeometricTail : Bool
    sourceHalfLogTwoRateFollowsFromRepairedTail : Bool
    mgfDomainMustBeRecomputedFromBlockRatio : Bool

canonicalRepairedMomentRateBoundary : RepairedMomentRateBoundary
canonicalRepairedMomentRateBoundary =
  repairedMomentRateBoundary true true true false true

polynomialMomentsSurviveRepair :
  RepairedMomentRateBoundary.allPolynomialMomentsFollowFromGeometricTail
    canonicalRepairedMomentRateBoundary
  ≡ true
polynomialMomentsSurviveRepair = refl

halfLogTwoDomainDoesNotSurviveRepair :
  RepairedMomentRateBoundary.sourceHalfLogTwoRateFollowsFromRepairedTail
    canonicalRepairedMomentRateBoundary
  ≡ false
halfLogTwoDomainDoesNotSurviveRepair = refl

record RateFormulaBoundary : Set where
  constructor rateFormulaBoundary
  field
    repairedRatioExpression : Bool
    repairedPerStepRateExpression : Bool
    universalRateClaim : Bool

canonicalRateFormulaBoundary : RateFormulaBoundary
canonicalRateFormulaBoundary =
  rateFormulaBoundary true true false

repairedRateExpressionOwned :
  RateFormulaBoundary.repairedPerStepRateExpression
    canonicalRateFormulaBoundary
  ≡ true
repairedRateExpressionOwned = refl
