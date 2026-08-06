module DASHI.Vision.Stereo4DDynamicReconstructionRegression where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)

open import DASHI.Geometry.SpacetimeHistoryWorldTube
open import DASHI.Vision.Stereo4DDynamicReconstructionBridge

imagePoint : SpatialSample
imagePoint = mkSpatialSample 240 180 0 "image pixel coordinates"

worldPoint : SpatialSample
worldPoint = mkSpatialSample 100 200 30 "Stereo4D pseudo-metric world frame"

canonicalFrame : StereoFrameReceipt
canonicalFrame =
  mkCandidateStereoFrameReceipt
    7
    42
    "left-frame-7"
    "right-frame-7"
    "optimized-camera-pose-7"
    "optimized-stereo-rig"
    "raft-disparity-7"

canonicalDynamicPoint : DynamicPointObservation
canonicalDynamicPoint =
  mkPseudoMetricDynamicPointObservation
    11
    7
    42
    imagePoint
    worldPoint
    trackedSubjectCandidateRole
    5
    3
    90
    true
    "Stereo4D-derived point track; arXiv:2412.09621v1"

canonicalCorrection : RayCorrectionReceipt
canonicalCorrection =
  mkRayCorrectionReceipt
    11
    7
    true
    refl
    2
    4
    1
    (1 ∷ 3 ∷ 5 ∷ [])
    true
    true
    refl

canonicalFilter : ReconstructionFilterReceipt
canonicalFilter =
  mkReconstructionFilterReceipt
    true
    true
    true
    true
    true
    true
    true
    "Stereo and temporal consistency checks passed"

canonicalReconstruction : DynamicReconstruction
canonicalReconstruction =
  mkDynamicReconstruction
    "VR180 stereo-video episode"
    paperReference
    (canonicalFrame ∷ [])
    (canonicalDynamicPoint ∷ [])
    (canonicalCorrection ∷ [])
    (canonicalFilter ∷ [])
    "first-camera world coordinate frame"
    true
    refl
    false
    refl
    true
    refl

canonicalPrediction : QueryTimeMotionPrediction
canonicalPrediction =
  mkQueryTimeMotionPrediction
    0
    10
    5
    "DynaDUSt3R pointmap"
    "DynaDUSt3R query-time motion map"
    "point confidence"
    "motion confidence"
    true
    true
    refl
    false
    refl

canonicalEnrichment : HistoryEnrichmentReceipt
canonicalEnrichment =
  mkCandidateHistoryEnrichment
    "candidate subject-local visual episode"
    canonicalDynamicPoint
    1
    1

canonicalFrameIsCandidate : frameCandidateOnly canonicalFrame ≡ true
canonicalFrameIsCandidate = refl

canonicalPointIsPseudoMetric : pointPseudoMetric canonicalDynamicPoint ≡ true
canonicalPointIsPseudoMetric = refl

canonicalPointIsNotExact : pointExactGroundTruth canonicalDynamicPoint ≡ false
canonicalPointIsNotExact = refl

canonicalReconstructionIsPseudoMetric :
  reconstructionPseudoMetric canonicalReconstruction ≡ true
canonicalReconstructionIsPseudoMetric = refl

canonicalReconstructionIsNotExact :
  reconstructionExact canonicalReconstruction ≡ false
canonicalReconstructionIsNotExact = refl

canonicalPredictionUsesLearnedPrior :
  predictionLearnedPrior canonicalPrediction ≡ true
canonicalPredictionUsesLearnedPrior = refl

canonicalPredictionIsNotExactTrajectory :
  predictionExactTrajectory canonicalPrediction ≡ false
canonicalPredictionIsNotExactTrajectory = refl

canonicalEnrichmentSeparatesMotionRoles :
  enrichmentCameraSceneSubjectSeparated canonicalEnrichment ≡ true
canonicalEnrichmentSeparatesMotionRoles = refl

canonicalEnrichmentDoesNotReplaceTimeline :
  enrichmentReplacesTimeline canonicalEnrichment ≡ false
canonicalEnrichmentDoesNotReplaceTimeline = refl

canonicalEnrichmentRemainsCandidateOnly :
  enrichmentCandidateOnly canonicalEnrichment ≡ true
canonicalEnrichmentRemainsCandidateOnly = refl
