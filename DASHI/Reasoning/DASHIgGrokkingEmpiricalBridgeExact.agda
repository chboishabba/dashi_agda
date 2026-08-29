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
-- Primary bounded empirical source surfaces at that commit:
--   README.md
--   .gitmodules
--   leech_arch_ablation_prelim/mul_adamw_lambda_0/scan.csv
--   plain_baseline_prelim/scan.csv
--   derivative_comparison_prelim.csv
--
-- ATTRIBUTION NOTE
-- The pinned DASHIg .gitmodules names SPUTNIKAI/LeechTransformer as the
-- upstream submodule URL.  A currently visible meta-introspector repository is
-- a separate clone/mirror-like surface whose repository metadata points its
-- homepage back to SPUTNIKAI/LeechTransformer.  Repository possession or clone
-- status is not authorship.
--
-- The mirrored README contains a software citation claiming:
--   A. Kornienko,
--   "Leech-Lila: A Geometric Attention Transformer via the Leech Lattice",
--   Zenodo DOI 10.5281/zenodo.18784424.
-- The original SPUTNIKAI GitHub endpoint was not available during this audit,
-- so that citation is retained as a secondary attribution claim, not promoted
-- here into independently verified primary authorship.
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
    "Representative-band geometry-variant/plain modular-multiplication runs and derivative-shape comparisons are preliminary empirical receipts for architecture/timing comparison."
    "Does not establish architecture superiority, a universal grokking timing law, a universal mechanism, large-seed robustness, or authorship of the upstream geometry-variant implementation."

------------------------------------------------------------------------
-- Upstream implementation attribution is kept separate from experiment
-- ownership.  The empirical rows below are owned as DASHIg experiment outputs;
-- that does not transfer authorship of imported architecture code to DASHIg,
-- chboishabba, or meta-introspector.
------------------------------------------------------------------------

data AttributionStatus : Set where
  secondaryCitationClaim primaryAttributionVerified : AttributionStatus

record UpstreamImplementationAttribution : Set where
  constructor upstreamImplementationAttribution
  field
    localSubmoduleName : String
    pinnedUpstreamURL : String
    mirrorRepository : String
    mirrorIsAuthorshipEvidence : Bool
    mirrorIsAuthorshipEvidenceIsFalse : mirrorIsAuthorshipEvidence ≡ false
    claimedAuthor : String
    claimedTitle : String
    claimedIdentifier : String
    status : AttributionStatus
    attributionReading : String

open UpstreamImplementationAttribution public

leechLilaAttribution : UpstreamImplementationAttribution
leechLilaAttribution =
  upstreamImplementationAttribution
    "LeechTransformer"
    "https://github.com/SPUTNIKAI/LeechTransformer.git"
    "github.com/meta-introspector/LeechTransformer"
    false refl
    "A. Kornienko (claimed by mirrored README citation; not independently promoted here)"
    "Leech-Lila: A Geometric Attention Transformer via the Leech Lattice"
    "Zenodo DOI 10.5281/zenodo.18784424 (citation claim in mirrored README)"
    secondaryCitationClaim
    "DASHIg pins the SPUTNIKAI submodule URL. The visible meta-introspector copy is not treated as authorship evidence. Until a primary archival/source record is independently verified, A. Kornienko/Zenodo metadata remain an explicitly secondary citation claim."

mirrorDoesNotConferAuthorship :
  mirrorIsAuthorshipEvidence leechLilaAttribution ≡ false
mirrorDoesNotConferAuthorship = refl

------------------------------------------------------------------------
-- Literal preliminary rows from the pinned DASHIg CSVs.
------------------------------------------------------------------------

data Architecture : Set where
  geometryVariantLambdaZero plainTransformer : Architecture

record PrelimGrokRow : Set where
  constructor prelimGrokRow
  field
    architecture : Architecture
    sourceModelLabel : String
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
-- 30 -> 0.30. It is not a floating-point theorem.
-- `sourceModelLabel` preserves the literal DASHIg CSV label without making an
-- authorship claim from the word "leech".

leechWd022 : PrelimGrokRow
leechWd022 =
  prelimGrokRow geometryVariantLambdaZero "leech_modular_classifier" 97 22 60 5060 5500 7260 true true

leechWd030 : PrelimGrokRow
leechWd030 =
  prelimGrokRow geometryVariantLambdaZero "leech_modular_classifier" 97 30 60 6220 12500 13200 true true

plainWd022 : PrelimGrokRow
plainWd022 =
  prelimGrokRow plainTransformer "plain_modular_transformer" 97 22 60 4520 6900 7360 true true

plainWd030 : PrelimGrokRow
plainWd030 =
  prelimGrokRow plainTransformer "plain_modular_transformer" 97 30 60 8320 9300 10840 true true

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
-- The CSV has n_runs = 2 for each architecture. Floating-point values remain
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

    dashigExperimentOwnershipImpliesUpstreamArchitectureAuthorship : Bool
    dashigExperimentOwnershipImpliesUpstreamArchitectureAuthorshipIsFalse :
      dashigExperimentOwnershipImpliesUpstreamArchitectureAuthorship ≡ false

    metaIntrospectorCloneImpliesMetaIntrospectorAuthorship : Bool
    metaIntrospectorCloneImpliesMetaIntrospectorAuthorshipIsFalse :
      metaIntrospectorCloneImpliesMetaIntrospectorAuthorship ≡ false

    secondaryReadmeCitationIsPrimaryAttributionReceipt : Bool
    secondaryReadmeCitationIsPrimaryAttributionReceiptIsFalse :
      secondaryReadmeCitationIsPrimaryAttributionReceipt ≡ false

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
    false refl
    false refl
    false refl
    true refl
    true refl
