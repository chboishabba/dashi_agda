module DASHI.Interop.SLRABCGoldBenchmarkRuntimeContractExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Interop.SLRWorldModelSuiteConvergenceRoadmapExact as Roadmap
import DASHI.Cognition.PNF.SensibLawDiscourseQualityAuditExact as Quality

------------------------------------------------------------------------
-- EXECUTABLE ABC 7.30 GOLD BENCHMARK CONTRACT
--
-- Runtime:
--   tools/slr-discourse-reconstruct/slr_abc_gold_benchmark.py
--   tools/slr-discourse-reconstruct/run_abc730_gold_benchmark.sh
--
-- The current primary ABC transcript gives explicit speaker labels.  It does
-- not give a complete gold annotation for quote/nesting semantics or calibrated
-- probabilities.  The first benchmark slice therefore scores only the labels
-- that are actually source-paid, while carrying the remaining benchmark
-- dimensions as explicit residuals.
------------------------------------------------------------------------

data GoldDimension : Set where
  speakerBoundaryPrecision : GoldDimension
  speakerBoundaryRecall : GoldDimension
  hiddenSpliceRecovery : GoldDimension
  hardCutRolePreservation : GoldDimension
  quoteNestingAccuracy : GoldDimension
  uncertaintyCalibration : GoldDimension
  residualFibreDelta : GoldDimension
  sourceRecoverability : GoldDimension


data GoldDimensionStatus : Set where
  executableScored : GoldDimensionStatus
  executableDiagnostic : GoldDimensionStatus
  notGoldLabelledYet : GoldDimensionStatus
  retainedFromExistingReceipt : GoldDimensionStatus

record GoldDimensionReceipt : Set where
  constructor goldDimensionReceipt
  field
    dimension : GoldDimension
    status : GoldDimensionStatus
    runtimeField : String
    sourceOfGold : String
    note : String

open GoldDimensionReceipt public

speakerPrecisionReceipt : GoldDimensionReceipt
speakerPrecisionReceipt = goldDimensionReceipt
  speakerBoundaryPrecision executableScored
  "speaker_boundary.precision_milli"
  "ABC official transcript explicit speaker labels aligned to noisy ASR"
  "Scores only hidden within-parser-sentence speaker changes that can be mapped with bounded word alignment."

speakerRecallReceipt : GoldDimensionReceipt
speakerRecallReceipt = goldDimensionReceipt
  speakerBoundaryRecall executableScored
  "speaker_boundary.recall_milli"
  "ABC official transcript explicit speaker labels aligned to noisy ASR"
  "Recall denominator is mapped hidden speaker-turn gold, not every programme speaker transition."

hiddenRecoveryReceipt : GoldDimensionReceipt
hiddenRecoveryReceipt = goldDimensionReceipt
  hiddenSpliceRecovery executableScored
  "hidden_splice.recovery_milli"
  "hard speaker cuts OR retained unresolved speaker-risk fibres"
  "Distinguishes exact hard-cut recovery from uncertainty-preserving recovery."

rolePreservationReceipt : GoldDimensionReceipt
rolePreservationReceipt = goldDimensionReceipt
  hardCutRolePreservation executableDiagnostic
  "role_preservation.hard_speaker_role_preservation_milli"
  "typed role-transition admission surface"
  "Structural consistency diagnostic; not an independent semantic gold label."

quoteNestingReceipt : GoldDimensionReceipt
quoteNestingReceipt = goldDimensionReceipt
  quoteNestingAccuracy notGoldLabelledYet
  "quote_nesting_accuracy.status=not-scored"
  "no independent quote/nesting gold annotation currently attached"
  "Punctuation or parser attachment is not promoted to quote/nesting gold truth."

uncertaintyReceipt : GoldDimensionReceipt
uncertaintyReceipt = goldDimensionReceipt
  uncertaintyCalibration notGoldLabelledYet
  "uncertainty_calibration.status=coverage-only-not-probability-calibrated"
  "residual fibre / risk flag coverage"
  "Coverage of missed gold boundaries is measurable; probabilistic calibration is not yet licensed."

residualDeltaReceipt : GoldDimensionReceipt
residualDeltaReceipt = goldDimensionReceipt
  residualFibreDelta notGoldLabelledYet
  "residual_fibre_delta.status=not-scored"
  "requires aligned candidate fibres across labelled/unlabelled runs"
  "Speaker labels alone do not provide a semantic residual-fibre gold standard."

sourceRecoverabilityReceipt : GoldDimensionReceipt
sourceRecoverabilityReceipt = goldDimensionReceipt
  sourceRecoverability retainedFromExistingReceipt
  "source_recoverability"
  "SLR_DISCOURSE_SPAN_INTEGRITY"
  "Benchmark reuses the byte-recoverability receipt rather than redefining source integrity."

------------------------------------------------------------------------
-- Reopening rule for the frozen cut arithmetic.
------------------------------------------------------------------------

data BenchmarkDefectKind : Set where
  precisionFailure : BenchmarkDefectKind
  recallFailure : BenchmarkDefectKind
  hiddenSpliceFailure : BenchmarkDefectKind
  rolePreservationFailure : BenchmarkDefectKind

record BenchmarkDefectReceipt : Set where
  constructor benchmarkDefectReceipt
  field
    defectKind : BenchmarkDefectKind
    benchmarkReference : String
    labelledCounterexampleReference : String
    parserHeuristicReopeningPermitted : Bool
    semanticTruthPromoted : Bool

open BenchmarkDefectReceipt public

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data SpeakerGoldImpliesQuoteNestingGold : Set where
data AlignmentMatchImpliesSemanticTruth : Set where
data HigherPrecisionPromotesPolicyClaim : Set where
data RiskCoverageIsProbabilityCalibration : Set where
data BenchmarkMayRewriteHistoricalSource : Set where

speakerGoldDoesNotCreateQuoteGold : SpeakerGoldImpliesQuoteNestingGold → ⊥
speakerGoldDoesNotCreateQuoteGold ()

alignmentDoesNotPromoteTruth : AlignmentMatchImpliesSemanticTruth → ⊥
alignmentDoesNotPromoteTruth ()

precisionDoesNotPromotePolicyTruth : HigherPrecisionPromotesPolicyClaim → ⊥
precisionDoesNotPromotePolicyTruth ()

riskCoverageIsNotCalibration : RiskCoverageIsProbabilityCalibration → ⊥
riskCoverageIsNotCalibration ()

benchmarkDoesNotRewriteSource : BenchmarkMayRewriteHistoricalSource → ⊥
benchmarkDoesNotRewriteSource ()

------------------------------------------------------------------------
-- Existing-owner anchors.
------------------------------------------------------------------------

roadmapBenchmarkAnchor : Roadmap.GoldDiscourseBenchmark
roadmapBenchmarkAnchor = Roadmap.abc730GoldBenchmarkPlan

qualityBoundaryAnchor : Quality.DiscourseQualityBoundary
qualityBoundaryAnchor = Quality.canonicalDiscourseQualityBoundary
