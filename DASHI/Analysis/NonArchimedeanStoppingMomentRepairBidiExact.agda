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
-- The final analytic consumer is standard and already theorem-bearing in
-- Mathlib.  In particular
--
--   `summable_pow_mul_exp_neg_nat_mul`
--
-- proves, for every k : Nat and every real r > 0,
--
--   Summable (fun n => n^k * exp (-r*n)).
--
-- Therefore any stopping tail dominated by exp (-alpha_m t), alpha_m > 0,
-- has every polynomial moment finite.  Exponential moments are finite only in
-- the repaired block-dependent strip Re(s) < alpha_m.  The old universal
-- Re(s) < (1/2) log 2 strip is not inherited.
--
-- Authority firewall:
--   dependency/source-library closure != Agda kernel-checking Mathlib's real
--   analysis theorem or the source probability-space identification.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)


data MomentLeaf : Set where
  finiteHittingBlock : MomentLeaf
  geometricBlockTail : MomentLeaf
  polynomialWeightedExponentialSeries : MomentLeaf
  allPolynomialMomentsFinite : MomentLeaf
  repairedExponentialMomentDomain : MomentLeaf
  sourceHalfLogTwoDomain : MomentLeaf


data MomentStatus : Set where
  repoOwned : MomentStatus
  sourceLibraryOwned : MomentStatus
  sourceLibraryCompiled : MomentStatus
  rejected : MomentStatus

momentStatus : MomentLeaf → MomentStatus
momentStatus finiteHittingBlock = repoOwned
momentStatus geometricBlockTail = repoOwned
momentStatus polynomialWeightedExponentialSeries = sourceLibraryOwned
momentStatus allPolynomialMomentsFinite = sourceLibraryCompiled
momentStatus repairedExponentialMomentDomain = sourceLibraryCompiled
momentStatus sourceHalfLogTwoDomain = rejected


data MomentObligation : Set where
  rejectedUniversalHalfLogTwoMGFDomain : MomentObligation

polynomialMomentCutset : List MomentObligation
polynomialMomentCutset = []

repairedMGFDomainCutset : List MomentObligation
repairedMGFDomainCutset = []

sourceMGFDomainDisposition : List MomentObligation
sourceMGFDomainDisposition = rejectedUniversalHalfLogTwoMGFDomain ∷ []

record MathlibMomentConsumerReceipt : Set where
  constructor mathlibMomentConsumerReceipt
  field
    theoremLocated : Bool
    polynomialWeightedExponentialSummable : Bool
    requiresPositiveRate : Bool
    enoughForAllPolynomialMoments : Bool
    agdaKernelChecksMathlibTheorem : Bool

canonicalMathlibMomentConsumerReceipt : MathlibMomentConsumerReceipt
canonicalMathlibMomentConsumerReceipt =
  mathlibMomentConsumerReceipt true true true true false

polynomialMomentConsumerDependencyClosed :
  polynomialMomentCutset ≡ []
polynomialMomentConsumerDependencyClosed = refl

record RepairedMomentRateBoundary : Set where
  constructor repairedMomentRateBoundary
  field
    blockTailRatioIsOneMinusTwoToMinusM : Bool
    rateDependsOnHittingBlockLength : Bool
    allPolynomialMomentsFollowFromGeometricTail : Bool
    sourceHalfLogTwoRateFollowsFromRepairedTail : Bool
    mgfDomainMustBeRecomputedFromBlockRatio : Bool
    repairedMGFDomainDependencyClosed : Bool

canonicalRepairedMomentRateBoundary : RepairedMomentRateBoundary
canonicalRepairedMomentRateBoundary =
  repairedMomentRateBoundary true true true false true true

polynomialMomentsSurviveRepair :
  RepairedMomentRateBoundary.allPolynomialMomentsFollowFromGeometricTail
    canonicalRepairedMomentRateBoundary
  ≡ true
polynomialMomentsSurviveRepair = refl

repairedMGFDomainClosed :
  RepairedMomentRateBoundary.repairedMGFDomainDependencyClosed
    canonicalRepairedMomentRateBoundary
  ≡ true
repairedMGFDomainClosed = refl

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
