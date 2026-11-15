module DASHI.Biology.BrainITTableReceiptsExact where

open import DASHI.Core.Prelude

import DASHI.Biology.BrainITSourceBoundaryExact as Source

------------------------------------------------------------------------
-- External paper values, NOT recomputed image reconstruction metrics.
--
-- Beliy, Zalcher, Kogman, Wasserman, Irani,
-- Brain-IT: Image Reconstruction from fMRI via Brain-Interaction Transformer
-- arXiv:2510.25976v2 (2026-03-01), ICLR 2026.
-- https://arxiv.org/html/2510.25976v2
-- Appendix A, Tables T2/T3; Appendix B, Table T7.
--
-- All metric values below are thousandths of one:
-- e.g. pixelCorrMilli 336 = 0.336; clipIDMilli 913 = 91.3%.
-- This makes decimal source transcription exact in Agda, but is NOT a
-- proof that the source's external ML evaluations were correctly run.
------------------------------------------------------------------------

data ClusteringPolicy : Set where
  functional : ClusteringPolicy
  threeDCoordinates : ClusteringPolicy
  schaefer400 : ClusteringPolicy
  schaefer1000 : ClusteringPolicy

record BrainITMetricRow : Set where
  constructor metricRow
  field
    pixelCorrMilli : Nat
    ssimMilli : Nat
    clipIDMilli : Nat
open BrainITMetricRow public

-- Table T7: subject 1 only; transfer from other subjects.
subjectOne15min : BrainITMetricRow
subjectOne15min = metricRow 336 476 913

subjectOne30min : BrainITMetricRow
subjectOne30min = metricRow 378 480 933

subjectOne60min : BrainITMetricRow
subjectOne60min = metricRow 396 484 947

-- Table T2: full-data results averaged over NSD subjects 1,2,5,7.
clusteringRow : ClusteringPolicy → BrainITMetricRow
clusteringRow functional = metricRow 386 486 964
clusteringRow threeDCoordinates = metricRow 378 491 956
clusteringRow schaefer400 = metricRow 371 477 961
clusteringRow schaefer1000 = metricRow 378 475 963

-- Table T3: only reported exemplar counts transcribed here. Full T3
-- must be retained at the paper when extending to additional metrics.
-- No fabricated zero for unreported cluster counts: use an indexed API.
data ReportedClusterCount : Set where
  eight : ReportedClusterCount
  oneTwentyEight : ReportedClusterCount
  fiveTwelve : ReportedClusterCount

reportedClusterPixelCorrMilli : ReportedClusterCount → Nat
reportedClusterPixelCorrMilli eight = 379
reportedClusterPixelCorrMilli oneTwentyEight = 386
reportedClusterPixelCorrMilli fiveTwelve = 392

record BrainITPaperReceipt : Set where
  constructor paperReceipt
  field
    paperIdentifier : String
    paperVersion : String
    benchmark : String
    transferSubject : Nat
    transfer15minSamples : Nat
    sourceTableTransfer : String
    sourceTableClustering : String
    sourceTableCounts : String
    publisherValuesTranscribed : Bool
    frozenEvaluatorCodeDigestPresent : Bool
    frozenModelCheckpointDigestPresent : Bool
    frozenDatasetSplitDigestPresent : Bool
    metricsIndependentlyRecomputed : Bool
    sourceValuesAreNeuralStateInverseProof : Bool
open BrainITPaperReceipt public

canonicalBrainITPaperReceipt : BrainITPaperReceipt
canonicalBrainITPaperReceipt =
  paperReceipt
    "Beliy et al.; arXiv:2510.25976"
    "v2 2026-03-01"
    "Natural Scenes Dataset (NSD)"
    1
    450
    "Appendix B, T7, subject 1"
    "Appendix A, T2, mean subjects 1,2,5,7"
    "Appendix A, T3, mean subjects 1,2,5,7"
    true false false false false false

-- Kernel-checked *transcription consistency*, not empirical calibration.
published15minPixelCorr :
  pixelCorrMilli subjectOne15min ≡ 336
published15minPixelCorr = refl

published15minSSIM :
  ssimMilli subjectOne15min ≡ 476
published15minSSIM = refl

published15minCLIP :
  clipIDMilli subjectOne15min ≡ 913
published15minCLIP = refl

paperSamplesMatchPrimarySourceBoundary :
  transfer15minSamples canonicalBrainITPaperReceipt ≡
  Source.BrainITSourceBoundary.fifteenMinuteSubjectOneSampleCount
    Source.canonicalBrainITSourceBoundary
paperSamplesMatchPrimarySourceBoundary = refl

functionalPixelCorrelationPaperValue :
  pixelCorrMilli (clusteringRow functional) ≡ 386
functionalPixelCorrelationPaperValue = refl

-- Critical nuance: spatial clustering scores higher on the particular
-- SSIM metric in T2; functional is not componentwise optimal.
threeDSpatialSSIMExceedsFunctionalInPublishedTable :
  ssimMilli (clusteringRow threeDCoordinates) ≡ 491
  × ssimMilli (clusteringRow functional) ≡ 486
threeDSpatialSSIMExceedsFunctionalInPublishedTable = refl , refl

reportOnlyNoEvaluatorReplay :
  metricsIndependentlyRecomputed canonicalBrainITPaperReceipt ≡ false
reportOnlyNoEvaluatorReplay = refl

reportOnlyNoCheckpointHash :
  frozenModelCheckpointDigestPresent canonicalBrainITPaperReceipt ≡ false
reportOnlyNoCheckpointHash = refl
