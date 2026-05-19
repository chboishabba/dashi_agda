module DASHI.Statistics.PrimeProfileStatsSuite where

open import Agda.Builtin.Bool using (Bool)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

open import Ontology.GodelLattice using (Vec15)

open import DASHI.Statistics.PrimeProfileStats as PPS using
  ( PrimeProfileStats
  ; primeProfileScore
  ; primeProfileWeights
  )
open import DASHI.Statistics.Vec15Descriptive as V15D using
  ( PrimeCarrier15
  ; sum15
  ; range15
  ; countNonZero15
  )
open import DASHI.Statistics.Vec15Robust as V15R using
  ( TukeyFence15
  ; iqr15
  ; tukeyFence15
  ; tukeyOutlierMask15
  ; hampelOutlierMask15
  ; winsorize15
  ; trimmedMean15
  ; mad15
  ; tukeySummary15
  ; hampelSummary15
  ; winsorizedSummary15
  )
open import DASHI.Statistics.Vec15Inference as V15I using
  ( InferenceSurface15
  ; ModelInput
  ; PairwiseModelInput
  ; anova15
  ; chiSquared15
  ; tTest15
  ; mannWhitney15
  ; kruskalWallis15
  ; pearsonCorrelation15
  ; spearmanCorrelation15
  ; regression15
  ; factorAnalysis15
  ; pca15
  ; cluster15
  ; modelInput15
  ; pairwiseModelInput15
  )

------------------------------------------------------------------------
-- Thin repo-facing integration surface for the prime-profile stats lane.
--
-- Descriptive stats are concrete already.
-- Robust stats are wired through the current Tukey / IQR surface.
-- Inference stats are wired through the current named operator surface and
-- the concrete model-input helpers.
--
-- The file stays compile-thin and does not invent extra semantics.

primeProfileModelInput :
  (profile : PrimeProfileStats) →
  ModelInput
primeProfileModelInput profile = modelInput15 (primeProfileWeights profile)

primeProfilePairwiseModelInput :
  (profile : PrimeProfileStats) →
  PairwiseModelInput
primeProfilePairwiseModelInput profile =
  pairwiseModelInput15
    (primeProfileWeights profile)
    (primeProfileWeights profile)

primeProfileInferenceSurface :
  (profile : PrimeProfileStats) →
  InferenceSurface15
primeProfileInferenceSurface profile = record
  { carrier = PrimeCarrier15
  ; carrier15 = primeProfileWeights profile
  ; anova = anova15
  ; chiSquared = chiSquared15
  ; tTest = tTest15
  ; mannWhitney = mannWhitney15
  ; kruskalWallis = kruskalWallis15
  ; pearsonCorrelation = pearsonCorrelation15
  ; spearmanCorrelation = spearmanCorrelation15
  ; regression = regression15
  ; factorAnalysis = factorAnalysis15
  ; pca = pca15
  ; cluster = cluster15
  }

record PrimeProfileRobustStats (profile : PrimeProfileStats) : Set₁ where
  field
    carrier : PrimeCarrier15
    carrierMatches :
      carrier ≡ primeProfileWeights profile

    interquartileRange : Nat
    interquartileRangeMatches :
      interquartileRange ≡ iqr15 carrier

    fence : TukeyFence15
    fenceMatches :
      fence ≡ tukeyFence15 carrier

    tukeyMask : Vec15 Bool
    tukeyMaskMatches :
      tukeyMask ≡ tukeyOutlierMask15 carrier

    hampelMask : Vec15 Bool
    hampelMaskMatches :
      hampelMask ≡ hampelOutlierMask15 carrier

    winsorizedCarrier : PrimeCarrier15
    winsorizedCarrierMatches :
      winsorizedCarrier ≡ winsorize15 carrier

    trimmedMean : Nat
    trimmedMeanMatches :
      trimmedMean ≡ trimmedMean15 carrier

    mad : Nat
    madMatches :
      mad ≡ mad15 carrier

    tukeySummary : Nat
    tukeySummaryMatches :
      tukeySummary ≡ tukeySummary15 carrier

    hampelSummary : Nat
    hampelSummaryMatches :
      hampelSummary ≡ hampelSummary15 carrier

    winsorizedSummary : Nat
    winsorizedSummaryMatches :
      winsorizedSummary ≡ winsorizedSummary15 carrier

primeProfileRobustStats :
  (profile : PrimeProfileStats) →
  PrimeProfileRobustStats profile
primeProfileRobustStats profile = record
  { carrier = primeProfileWeights profile
  ; carrierMatches = refl
  ; interquartileRange = iqr15 (primeProfileWeights profile)
  ; interquartileRangeMatches = refl
  ; fence = tukeyFence15 (primeProfileWeights profile)
  ; fenceMatches = refl
  ; tukeyMask = tukeyOutlierMask15 (primeProfileWeights profile)
  ; tukeyMaskMatches = refl
  ; hampelMask = hampelOutlierMask15 (primeProfileWeights profile)
  ; hampelMaskMatches = refl
  ; winsorizedCarrier = winsorize15 (primeProfileWeights profile)
  ; winsorizedCarrierMatches = refl
  ; trimmedMean = trimmedMean15 (primeProfileWeights profile)
  ; trimmedMeanMatches = refl
  ; mad = mad15 (primeProfileWeights profile)
  ; madMatches = refl
  ; tukeySummary = tukeySummary15 (primeProfileWeights profile)
  ; tukeySummaryMatches = refl
  ; hampelSummary = hampelSummary15 (primeProfileWeights profile)
  ; hampelSummaryMatches = refl
  ; winsorizedSummary = winsorizedSummary15 (primeProfileWeights profile)
  ; winsorizedSummaryMatches = refl
  }

record PrimeProfileInferenceStats (profile : PrimeProfileStats) : Set₁ where
  field
    surface : InferenceSurface15
    surfaceMatches :
      surface ≡ primeProfileInferenceSurface profile

    modelInput : ModelInput
    modelInputMatches :
      modelInput ≡ primeProfileModelInput profile

    pairwiseModelInput : PairwiseModelInput
    pairwiseModelInputMatches :
      pairwiseModelInput ≡ primeProfilePairwiseModelInput profile

primeProfileInferenceStats :
  (profile : PrimeProfileStats) →
  PrimeProfileInferenceStats profile
primeProfileInferenceStats profile = record
  { surface = primeProfileInferenceSurface profile
  ; surfaceMatches = refl
  ; modelInput = primeProfileModelInput profile
  ; modelInputMatches = refl
  ; pairwiseModelInput = primeProfilePairwiseModelInput profile
  ; pairwiseModelInputMatches = refl
  }

record PrimeProfileStatsSuite : Set₁ where
  field
    profile : PrimeProfileStats

    descriptiveCarrier : PrimeCarrier15
    descriptiveCarrierMatches :
      descriptiveCarrier ≡ primeProfileWeights profile

    descriptiveScore : Nat
    descriptiveScoreMatches :
      descriptiveScore ≡ sum15 descriptiveCarrier

    descriptiveRange : Nat
    descriptiveRangeMatches :
      descriptiveRange ≡ range15 descriptiveCarrier

    descriptiveNonZeroCount : Nat
    descriptiveNonZeroCountMatches :
      descriptiveNonZeroCount ≡ countNonZero15 descriptiveCarrier

    primeProfileScoreMatches :
      descriptiveScore ≡ primeProfileScore profile

    robustStats : PrimeProfileRobustStats profile
    inferenceStats : PrimeProfileInferenceStats profile

primeProfileStatsSuite : PrimeProfileStats → PrimeProfileStatsSuite
primeProfileStatsSuite profile = record
  { profile = profile
  ; descriptiveCarrier = primeProfileWeights profile
  ; descriptiveCarrierMatches = refl
  ; descriptiveScore = sum15 (primeProfileWeights profile)
  ; descriptiveScoreMatches = refl
  ; descriptiveRange = range15 (primeProfileWeights profile)
  ; descriptiveRangeMatches = refl
  ; descriptiveNonZeroCount = countNonZero15 (primeProfileWeights profile)
  ; descriptiveNonZeroCountMatches = refl
  ; primeProfileScoreMatches = refl
  ; robustStats = primeProfileRobustStats profile
  ; inferenceStats = primeProfileInferenceStats profile
  }

open PrimeProfileStatsSuite public
