module DASHI.Vision.Stereo4DDynamicReconstructionBridge where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

open import DASHI.Geometry.SpacetimeHistoryTypedCore
open import DASHI.Geometry.SpacetimeHistoryScaleHierarchy

------------------------------------------------------------------------
-- Credit: Linyi Jin, Richard Tucker, Zhengqi Li, David Fouhey,
-- Noah Snavely, and Aleksander Holynski,
-- "Stereo4D: Learning How Things Move in 3D from Internet Stereo Videos",
-- arXiv:2412.09621v1 (2024).

paperReference : String
paperReference = "Jin et al., Stereo4D, arXiv:2412.09621v1 (2024)"

data MotionRole : Set where
  cameraRigMotion : MotionRole
  staticScenePoint : MotionRole
  dynamicScenePoint : MotionRole
  candidateSubjectPoint : MotionRole
  unknownMotion : MotionRole

record StereoFrameReceipt : Set where
  constructor stereoFrameReceipt
  field frameIndex : Nat
        frameTime : Timestamp
        leftImageReference : String
        rightImageReference : String
        cameraPoseReference : String
        stereoCalibrationReference : String
        disparityReference : String
open StereoFrameReceipt public

record DynamicPointObservation : Set where
  constructor dynamicPointObservation
  field trackIndex : Nat
        frameIndex : Nat
        pointTime : Timestamp
        imageCoordinate : PixelCoordinate
        worldCoordinate : WorldCoordinate
        motionRole : MotionRole
        depthUncertainty : Metres
        trackConfidence : Confidence
        pseudoMetric : Bool
        pseudoMetricIsTrue : pseudoMetric ≡ true
        exactGroundTruth : Bool
        exactGroundTruthIsFalse : exactGroundTruth ≡ false
        provenance : String
open DynamicPointObservation public

record RayCorrectionReceipt : Set where
  constructor rayCorrectionReceipt
  field correctedTrack : Nat
        correctedFrame : Nat
        alongCameraRay : Bool
        alongCameraRayIsTrue : alongCameraRay ≡ true
        staticConsistencyTerm : Nat
        dynamicAccelerationTerm : Nat
        disparityFaithfulnessTerm : Nat
open RayCorrectionReceipt public

record DynamicReconstruction : Set where
  constructor dynamicReconstruction
  field reconstructionSource : String
        reconstructionCitation : String
        reconstructionFrames : List StereoFrameReceipt
        reconstructionPoints : List DynamicPointObservation
        reconstructionCorrections : List RayCorrectionReceipt
        reconstructionPseudoMetric : Bool
        reconstructionPseudoMetricIsTrue : reconstructionPseudoMetric ≡ true
        reconstructionExact : Bool
        reconstructionExactIsFalse : reconstructionExact ≡ false
        cameraSceneSubjectSeparated : Bool
        cameraSceneSubjectSeparatedIsTrue : cameraSceneSubjectSeparated ≡ true
open DynamicReconstruction public

mkCandidateDynamicReconstruction :
  String → List StereoFrameReceipt → List DynamicPointObservation →
  List RayCorrectionReceipt → DynamicReconstruction
mkCandidateDynamicReconstruction source frames points corrections =
  dynamicReconstruction source paperReference frames points corrections
    true refl false refl true refl

pointToTypedObservation : String → MotionMode → DynamicPointObservation → TypedObservation
pointToTypedObservation place mode point =
  typedObservation
    (trackIndex point)
    (pointTime point)
    (worldCoordinate point)
    (depthUncertainty point)
    (trackConfidence point)
    mode place (provenance point)

record Stereo4DHistoryEnrichment : Set where
  constructor stereo4DHistoryEnrichment
  field localPoint : DynamicPointObservation
        coarseObservation : TypedObservation
        enrichmentLaw : NonReplacementLaw
          (pointToTypedObservation (observedPlace coarseObservation)
            (observedMode coarseObservation) localPoint)
          coarseObservation
        replacesHistory : Bool
        replacesHistoryIsFalse : replacesHistory ≡ false
open Stereo4DHistoryEnrichment public

mkStereo4DHistoryEnrichment :
  (point : DynamicPointObservation) →
  (coarse : TypedObservation) → Stereo4DHistoryEnrichment
mkStereo4DHistoryEnrichment point coarse =
  stereo4DHistoryEnrichment point coarse
    (canonicalNonReplacement
      (pointToTypedObservation (observedPlace coarse) (observedMode coarse) point)
      coarse)
    false refl
