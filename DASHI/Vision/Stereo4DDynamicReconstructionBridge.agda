module DASHI.Vision.Stereo4DDynamicReconstructionBridge where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Unit using (⊤)

open import DASHI.Geometry.SpacetimeHistoryWorldTube
  using
    ( SpatialSample
    ; TimelineObservation
    ; WorldTubeSection
    ; mkUncertainTimelineObservation
    ; mkWorldTubeSection
    ; unknownMode
    )

------------------------------------------------------------------------
-- Candidate-only bridge for:
--
-- Linyi Jin, Richard Tucker, Zhengqi Li, David Fouhey, Noah Snavely,
-- Aleksander Holynski, "Stereo4D: Learning How Things Move in 3D from
-- Internet Stereo Videos", arXiv:2412.09621v1 (2024).
--
-- The paper mines pseudo-metric dynamic 3D reconstructions from VR180
-- stereo video by combining camera-pose estimation, stereo disparity/depth,
-- long-range 2D tracks, world-frame lifting, ray-wise denoising, confidence
-- checks, semantic filtering, and quality control.
--
-- This module credits and types that pipeline without claiming that a learned
-- reconstruction is exact geometry, ground-truth experience, identity, or
-- surveillance authority.

paperTitle : String
paperTitle = "Stereo4D: Learning How Things Move in 3D from Internet Stereo Videos"

paperAuthors : String
paperAuthors =
  "Linyi Jin; Richard Tucker; Zhengqi Li; David Fouhey; Noah Snavely; Aleksander Holynski"

paperReference : String
paperReference = "arXiv:2412.09621v1 (2024)"

data Never : Set where

data Stereo4DRoute : Set where
  candidateReconstructionRoute : Stereo4DRoute
  exactMetricGroundTruthRoute : Stereo4DRoute
  imagePairDeterminesUniqueWorldRoute : Stereo4DRoute
  reconstructedTrackEqualsLivedHistoryRoute : Stereo4DRoute
  identityInferenceAuthorityRoute : Stereo4DRoute
  surveillanceAuthorityRoute : Stereo4DRoute

AdmissibleStereo4DRoute : Stereo4DRoute → Set
AdmissibleStereo4DRoute candidateReconstructionRoute = ⊤
AdmissibleStereo4DRoute exactMetricGroundTruthRoute = Never
AdmissibleStereo4DRoute imagePairDeterminesUniqueWorldRoute = Never
AdmissibleStereo4DRoute reconstructedTrackEqualsLivedHistoryRoute = Never
AdmissibleStereo4DRoute identityInferenceAuthorityRoute = Never
AdmissibleStereo4DRoute surveillanceAuthorityRoute = Never

exactMetricGroundTruthRejected :
  AdmissibleStereo4DRoute exactMetricGroundTruthRoute → Never
exactMetricGroundTruthRejected impossible = impossible

imagePairDeterminesUniqueWorldRejected :
  AdmissibleStereo4DRoute imagePairDeterminesUniqueWorldRoute → Never
imagePairDeterminesUniqueWorldRejected impossible = impossible

reconstructedTrackEqualsLivedHistoryRejected :
  AdmissibleStereo4DRoute reconstructedTrackEqualsLivedHistoryRoute → Never
reconstructedTrackEqualsLivedHistoryRejected impossible = impossible

identityInferenceAuthorityRejected :
  AdmissibleStereo4DRoute identityInferenceAuthorityRoute → Never
identityInferenceAuthorityRejected impossible = impossible

surveillanceAuthorityRejected :
  AdmissibleStereo4DRoute surveillanceAuthorityRoute → Never
surveillanceAuthorityRejected impossible = impossible

data ReconstructionStage : Set where
  stereoFrameIntakeStage : ReconstructionStage
  shotSegmentationStage : ReconstructionStage
  cameraPoseStage : ReconstructionStage
  stereoCalibrationStage : ReconstructionStage
  disparityDepthStage : ReconstructionStage
  twoDimensionalTrackStage : ReconstructionStage
  worldFrameLiftStage : ReconstructionStage
  rayCorrectionStage : ReconstructionStage
  temporalDenoisingStage : ReconstructionStage
  confidenceFilterStage : ReconstructionStage
  semanticDriftFilterStage : ReconstructionStage
  dynamicPointCloudStage : ReconstructionStage

data MotionRole : Set where
  cameraRigMotionRole : MotionRole
  staticScenePointRole : MotionRole
  dynamicScenePointRole : MotionRole
  trackedSubjectCandidateRole : MotionRole
  unknownMotionRole : MotionRole

data ObjectiveTerm : Set where
  staticConsistencyTerm : ObjectiveTerm
  dynamicAccelerationTerm : ObjectiveTerm
  disparityFaithfulnessTerm : ObjectiveTerm
  pointmapRegressionTerm : ObjectiveTerm
  displacedPositionRegressionTerm : ObjectiveTerm
  confidenceCalibrationTerm : ObjectiveTerm

data MeasurementKind : Set where
  leftImageMeasurement : MeasurementKind
  rightImageMeasurement : MeasurementKind
  cameraExtrinsicMeasurement : MeasurementKind
  stereoRigMeasurement : MeasurementKind
  disparityMeasurement : MeasurementKind
  depthMeasurement : MeasurementKind
  imageTrackMeasurement : MeasurementKind
  worldPointMeasurement : MeasurementKind
  motionVectorMeasurement : MeasurementKind
  confidenceMeasurement : MeasurementKind

record StereoFrameReceipt : Set where
  constructor mkStereoFrameReceipt
  field
    frameIndex : Nat
    frameTime : Nat
    leftImageReference : String
    rightImageReference : String
    cameraPoseReference : String
    stereoCalibrationReference : String
    disparityReference : String
    frameCandidateOnly : Bool
    frameCandidateOnlyIsTrue : frameCandidateOnly ≡ true
open StereoFrameReceipt public

mkCandidateStereoFrameReceipt :
  Nat → Nat → String → String → String → String → String → StereoFrameReceipt
mkCandidateStereoFrameReceipt index time left right pose rig disparity =
  mkStereoFrameReceipt index time left right pose rig disparity true refl

record DynamicPointObservation : Set where
  constructor mkDynamicPointObservation
  field
    pointTrackIndex : Nat
    pointFrameIndex : Nat
    pointTime : Nat
    pointImageCoordinate : SpatialSample
    pointWorldCoordinate : SpatialSample
    pointMotionRole : MotionRole
    pointDepthUncertainty : Nat
    pointTrackUncertainty : Nat
    pointConfidence : Nat
    pointVisible : Bool
    pointPseudoMetric : Bool
    pointPseudoMetricIsTrue : pointPseudoMetric ≡ true
    pointExactGroundTruth : Bool
    pointExactGroundTruthIsFalse : pointExactGroundTruth ≡ false
    pointProvenance : String
open DynamicPointObservation public

mkPseudoMetricDynamicPointObservation :
  Nat → Nat → Nat → SpatialSample → SpatialSample → MotionRole →
  Nat → Nat → Nat → Bool → String → DynamicPointObservation
mkPseudoMetricDynamicPointObservation track frame time imagePoint worldPoint role depthU trackU confidence visible provenance =
  mkDynamicPointObservation
    track frame time imagePoint worldPoint role depthU trackU confidence visible
    true refl false refl provenance

record RayCorrectionReceipt : Set where
  constructor mkRayCorrectionReceipt
  field
    correctionTrackIndex : Nat
    correctionFrameIndex : Nat
    correctionAlongCameraRay : Bool
    correctionAlongCameraRayIsTrue : correctionAlongCameraRay ≡ true
    correctionStaticTerm : Nat
    correctionDynamicTerm : Nat
    correctionDisparityTerm : Nat
    correctionWindowScales : List Nat
    correctionOptimized : Bool
    correctionCandidateOnly : Bool
    correctionCandidateOnlyIsTrue : correctionCandidateOnly ≡ true
open RayCorrectionReceipt public

record ReconstructionFilterReceipt : Set where
  constructor mkReconstructionFilterReceipt
  field
    filterStereoHorizontalConsistency : Bool
    filterStereoCycleConsistency : Bool
    filterTrackOverlapPruned : Bool
    filterSemanticStaticDriftPruned : Bool
    filterCrossFadePruned : Bool
    filterSyntheticOverlayPruned : Bool
    filterPassing : Bool
    filterClaim : String
open ReconstructionFilterReceipt public

record DynamicReconstruction : Set where
  constructor mkDynamicReconstruction
  field
    reconstructionSource : String
    reconstructionCitation : String
    reconstructionFrames : List StereoFrameReceipt
    reconstructionPoints : List DynamicPointObservation
    reconstructionCorrections : List RayCorrectionReceipt
    reconstructionFilters : List ReconstructionFilterReceipt
    reconstructionCoordinateFrame : String
    reconstructionPseudoMetric : Bool
    reconstructionPseudoMetricIsTrue : reconstructionPseudoMetric ≡ true
    reconstructionExact : Bool
    reconstructionExactIsFalse : reconstructionExact ≡ false
    reconstructionCandidateOnly : Bool
    reconstructionCandidateOnlyIsTrue : reconstructionCandidateOnly ≡ true
open DynamicReconstruction public

record QueryTimeMotionPrediction : Set where
  constructor mkQueryTimeMotionPrediction
  field
    predictionFirstFrame : Nat
    predictionSecondFrame : Nat
    predictionQueryTime : Nat
    predictionPointmapReference : String
    predictionMotionMapReference : String
    predictionPointConfidenceReference : String
    predictionMotionConfidenceReference : String
    predictionScaleAligned : Bool
    predictionLearnedPrior : Bool
    predictionLearnedPriorIsTrue : predictionLearnedPrior ≡ true
    predictionExactTrajectory : Bool
    predictionExactTrajectoryIsFalse : predictionExactTrajectory ≡ false
open QueryTimeMotionPrediction public

------------------------------------------------------------------------
-- Integration seam into the existing spacetime-history world-tube.
--
-- A reconstructed scene-point trajectory may thicken or locally enrich one
-- recorded episode.  It does not silently become the subject's personal
-- trajectory: camera motion, scene motion, and subject motion remain distinct.

record HistoryEnrichmentReceipt : Set where
  constructor mkHistoryEnrichmentReceipt
  field
    enrichmentPoint : DynamicPointObservation
    enrichmentHistoryObservation : TimelineObservation
    enrichmentWorldTubeSection : WorldTubeSection
    enrichmentRole : MotionRole
    enrichmentCameraSceneSubjectSeparated : Bool
    enrichmentCameraSceneSubjectSeparatedIsTrue :
      enrichmentCameraSceneSubjectSeparated ≡ true
    enrichmentReplacesTimeline : Bool
    enrichmentReplacesTimelineIsFalse : enrichmentReplacesTimeline ≡ false
    enrichmentCandidateOnly : Bool
    enrichmentCandidateOnlyIsTrue : enrichmentCandidateOnly ≡ true
open HistoryEnrichmentReceipt public

mkCandidateHistoryEnrichment :
  String → DynamicPointObservation → Nat → Nat → HistoryEnrichmentReceipt
mkCandidateHistoryEnrichment subject point temporalThickness meaningWeight =
  let
    uncertainty = pointDepthUncertainty point
    observation =
      mkUncertainTimelineObservation
        (pointTrackIndex point)
        (pointTime point)
        subject
        (pointWorldCoordinate point)
        uncertainty
        unknownMode
        (pointProvenance point)
    section =
      mkWorldTubeSection observation uncertainty temporalThickness meaningWeight
  in
  mkHistoryEnrichmentReceipt
    point observation section (pointMotionRole point)
    true refl false refl true refl

canonicalStereo4DStages : List ReconstructionStage
canonicalStereo4DStages =
  stereoFrameIntakeStage
  ∷ shotSegmentationStage
  ∷ cameraPoseStage
  ∷ stereoCalibrationStage
  ∷ disparityDepthStage
  ∷ twoDimensionalTrackStage
  ∷ worldFrameLiftStage
  ∷ rayCorrectionStage
  ∷ temporalDenoisingStage
  ∷ confidenceFilterStage
  ∷ semanticDriftFilterStage
  ∷ dynamicPointCloudStage
  ∷ []

canonicalStereo4DObjectiveTerms : List ObjectiveTerm
canonicalStereo4DObjectiveTerms =
  staticConsistencyTerm
  ∷ dynamicAccelerationTerm
  ∷ disparityFaithfulnessTerm
  ∷ pointmapRegressionTerm
  ∷ displacedPositionRegressionTerm
  ∷ confidenceCalibrationTerm
  ∷ []

canonicalStereo4DNotes : List String
canonicalStereo4DNotes =
  "Stereo4D is credited as the source of the reconstruction pipeline formalized here"
  ∷ "Stereo video supplies a known-baseline route to pseudo-metric depth"
  ∷ "Camera pose, stereo disparity, and 2D tracks are fused in a shared world frame"
  ∷ "Ray-wise correction preserves measurement provenance while reducing temporal jitter"
  ∷ "Static and dynamic tracks receive different smoothness pressure"
  ∷ "Disparity-space fidelity represents distance-dependent depth uncertainty"
  ∷ "Camera motion, scene-point motion, and candidate subject motion remain distinct roles"
  ∷ "A learned query-time motion map is a prior-mediated prediction, not an exact trajectory"
  ∷ "A reconstructed visual episode can enrich but cannot replace a personal timeline history"
  ∷ "No identity, lived-experience, or surveillance authority is promoted"
  ∷ []
