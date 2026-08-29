module DASHI.Reasoning.DASHIgGrokkingEmpiricalBridgeExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- DASHIg GROKKING EMPIRICAL BRIDGE
--
-- Internal empirical provenance, distinct from the external Prakash--Martin
-- anti-grokking source profile.
--
-- Pinned producer repository:
--   chboishabba/DASHIg
--   commit 013962fb839e83ce8e4b35486fe1a79792c96db8
--
-- Primary bounded source surfaces at that commit:
--   README.md
--   leech_arch_ablation_prelim/mul_adamw_lambda_0/scan.csv
--   plain_baseline_prelim/scan.csv
--   derivative_comparison_prelim.csv
--
-- The repository itself states that Phase 1 baseline ownership is dashifine,
-- Phase 2 comparison/validation ownership is DASHIg, and the broader formalism
-- is dashi_agda.  The representative-band results are explicitly preliminary
-- and directional rather than final large-seed evidence.
------------------------------------------------------------------------

record InternalEmpiricalSource : Set where
  constructor internalEmpiricalSource
  field
    repository : String
    commit : String
    ownershipReading : String
    boundedReading : String
    excludedPromotion : String

open InternalEmpiricalSource public

canonicalDASHIgPhase2Source : InternalEmpiricalSource
canonicalDASHIgPhase2Source =
  internalEmpiricalSource
    "github.com/chboishabba/DASHIg"
    "013962fb839e83ce8e4b35486fe1a79792c96db8"
    "Phase 2 comparison and validation harness for grokking dynamics; Phase 1 baseline belongs to dashifine and formal contracts belong to dashi_agda."
    "Representative-band Leech/plain modular-multiplication runs and derivative-shape comparisons are preliminary empirical receipts for architecture/timing comparison."
    "Does not establish Leech superiority, a universal grokking timing law, a universal mechanism, or large-seed robustness."

------------------------------------------------------------------------
-- Literal preliminary rows from the pinned CSVs.
------------------------------------------------------------------------

data Architecture : Set where
  leechLambdaZero plainTransformer : Architecture

record PrelimGrokRow : Set where
  constructor prelimGrokRow
  field
    architecture : Architecture
    modulus : Nat
    weightDecayCode : Nat
    tFit : Nat
    t50 : Nat
    t95 : Nat
    stopEpoch : Nat
    finalTrainPerfect : Bool
    finalTestPerfect : Bool

open PrelimGrokRow public

-- weightDecayCode uses hundredths solely as a finite exact code: 22 -> 0.22,
-- 30 -> 0.30.  It is not a floating-point theorem.

leechWd022 : PrelimGrokRow
leechWd022 = prelimGrokRow leechLambdaZero 97 22 60 5060 5500 7260 true true

leechWd030 : PrelimGrokRow
leechWd030 = prelimGrokRow leechLambdaZero 97 30 60 6220 12500 13200 true true

plainWd022 : PrelimGrokRow
plainWd022 = prelimGrokRow plainTransformer 97 22 60 4520 6900 7360 true true

plainWd030 : PrelimGrokRow
plainWd030 = prelimGrokRow plainTransformer 97 30 60 8320 9300 10840 true true

leech022T50Is5060 : t50 leechWd022 ≡ 5060
leech022T50Is5060 = refl

leech030T50Is6220 : t50 leechWd030 ≡ 6220
leech030T50Is6220 = refl

plain022T50Is4520 : t50 plainWd022 ≡ 4520
plain022T50Is4520 = refl

plain030T50Is8320 : t50 plainWd030 ≡ 8320
plain030T50Is8320 = refl

allFourPrelimRunsReachPerfectFinalAccuracy :
  (finalTrainPerfect leechWd022 ≡ true)
  × (finalTestPerfect leechWd022 ≡ true)
  × (finalTrainPerfect leechWd030 ≡ true)
  × (finalTestPerfect leechWd030 ≡ true)
  × (finalTrainPerfect plainWd022 ≡ true)
  × (finalTestPerfect plainWd022 ≡ true)
  × (finalTrainPerfect plainWd030 ≡ true)
  × (finalTestPerfect plainWd030 ≡ true)
allFourPrelimRunsReachPerfectFinalAccuracy =
  refl , refl , refl , refl , refl , refl , refl , refl

------------------------------------------------------------------------
-- Derivative-comparison provenance.
--
-- The CSV has n_runs = 2 for each architecture.  Floating-point values remain
-- source data, represented as strings here rather than promoted into exact
-- rational equalities.
------------------------------------------------------------------------

record DerivativePrelimSummary : Set where
  constructor derivativePrelimSummary
  field
    label : String
    meanPeakX : String
    meanSlopeProxyK : String
    meanCorrelationToMean : String
    runCount : Nat

open DerivativePrelimSummary public

leechDerivativePrelim : DerivativePrelimSummary
leechDerivativePrelim =
  derivativePrelimSummary
    "leech_lambda_0"
    "1.06875"
    "56.18513226650979"
    "0.7608355738736535"
    2

plainDerivativePrelim : DerivativePrelimSummary
plainDerivativePrelim =
  derivativePrelimSummary
    "plain_baseline"
    "1.2712500000000002"
    "56.44688505785779"
    "0.7668887699554757"
    2

bothDerivativeSummariesAreTwoRunPrelims :
  (runCount leechDerivativePrelim ≡ 2)
  × (runCount plainDerivativePrelim ≡ 2)
bothDerivativeSummariesAreTwoRunPrelims = refl , refl

------------------------------------------------------------------------
-- Attribution / interpretation boundary.
------------------------------------------------------------------------

record DASHIgGrokkingEmpiricalBoundary : Set where
  constructor dashiGGrokkingEmpiricalBoundary
  field
    dashigPrelimIsPrakashMartinReproduction : Bool
    dashigPrelimIsPrakashMartinReproductionIsFalse :
      dashigPrelimIsPrakashMartinReproduction ≡ false

    twoRunDerivativeTableEstablishesArchitectureSuperiority : Bool
    twoRunDerivativeTableEstablishesArchitectureSuperiorityIsFalse :
      twoRunDerivativeTableEstablishesArchitectureSuperiority ≡ false

    perfectFinalAccuracyIdentifiesLearningMechanism : Bool
    perfectFinalAccuracyIdentifiesLearningMechanismIsFalse :
      perfectFinalAccuracyIdentifiesLearningMechanism ≡ false

    preliminaryTimingDifferenceCanFeedExperimentInference : Bool
    preliminaryTimingDifferenceCanFeedExperimentInferenceIsTrue :
      preliminaryTimingDifferenceCanFeedExperimentInference ≡ true

    phase2ProducerMustRemainPinnedToRepositoryCommit : Bool
    phase2ProducerMustRemainPinnedToRepositoryCommitIsTrue :
      phase2ProducerMustRemainPinnedToRepositoryCommit ≡ true

canonicalDASHIgGrokkingEmpiricalBoundary : DASHIgGrokkingEmpiricalBoundary
canonicalDASHIgGrokkingEmpiricalBoundary =
  dashiGGrokkingEmpiricalBoundary
    false refl
    false refl
    false refl
    true refl
    true refl
