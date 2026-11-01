module DASHI.Cognition.PNF.SensibLawABC730DiscourseCutV2SuccessReceiptExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Empirical receipt: slr-discourse-cut-v2 on the retained ABC 7.30 specimen.
-- These are observed ranking results, not proof of speaker identity or a
-- general accuracy theorem.
------------------------------------------------------------------------

record CutBenchmarkResult : Set where
  constructor cutBenchmarkResult
  field
    sentence : String
    split : String
    expectedBoundary : String
    unprofiledRank : String
    profiledRank : String
    unprofiledScore : String
    profiledScore : String
    interpretation : String

open CutBenchmarkResult public

shoebridgeLeeserV2 : CutBenchmarkResult
shoebridgeLeeserV2 = cutBenchmarkResult
  "45" "7"
  "David Shoebridge -> Julian Leeser candidate broadcast cut"
  "1" "1" "22" "28"
  "The known/likely cut is the highest-ranked candidate in sentence 45 and the joint 42/45 pool in both runs."

wongHusicV2 : CutBenchmarkResult
wongHusicV2 = cutBenchmarkResult
  "42" "35"
  "Penny Wong/reporter material -> Ed Husic quote"
  "3" "5" "11" "18"
  "The target boundary remains in the top tier after residual de-biasing and sentiment gating."

record RepairValidation : Set where
  constructor repairValidation
  field
    residualBiasRemoved : Bool
    vaderDistractorSuppressed : Bool
    hyphenProfileNormalizationObserved : Bool
    coordinationCrossingRepairObserved : Bool
    transcriptWideCandidateGenerationAdmitted : Bool
    automaticSpeakerVerificationAdmitted : Bool
    automaticSpeakerVerificationAdmittedIsFalse : automaticSpeakerVerificationAdmitted ≡ false

canonicalRepairValidation : RepairValidation
canonicalRepairValidation = repairValidation
  true true true true true false refl

------------------------------------------------------------------------
-- Promotion boundary.
------------------------------------------------------------------------

record V2BenchmarkBoundary : Set where
  constructor v2BenchmarkBoundary
  field
    localSuccessProvesGeneralAccuracy : Bool
    localSuccessProvesGeneralAccuracyIsFalse : localSuccessProvesGeneralAccuracy ≡ false
    goldLabelsMayBeUsedAfterScoring : Bool
    goldLabelsMayBeUsedAfterScoringIsTrue : goldLabelsMayBeUsedAfterScoring ≡ true
    goldLabelsMayEnterBlindScorer : Bool
    goldLabelsMayEnterBlindScorerIsFalse : goldLabelsMayEnterBlindScorer ≡ false
    transcriptWideRunMayGenerateCandidates : Bool
    transcriptWideRunMayGenerateCandidatesIsTrue : transcriptWideRunMayGenerateCandidates ≡ true

canonicalV2BenchmarkBoundary : V2BenchmarkBoundary
canonicalV2BenchmarkBoundary = v2BenchmarkBoundary false refl true refl false refl true refl
