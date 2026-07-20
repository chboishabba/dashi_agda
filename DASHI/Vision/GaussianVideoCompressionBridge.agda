module DASHI.Vision.GaussianVideoCompressionBridge where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Unit using (⊤; tt)

open import DASHI.Geometry.SpacetimeHistoryWorldTube
open import DASHI.Vision.Stereo4DDynamicReconstructionBridge

------------------------------------------------------------------------
-- Candidate-only GaussianVideo representation/compression bridge.
--
-- Paper credit:
--   Inseo Lee, Youngyoon Choi, and Joonseok Lee,
--   "GaussianVideo: Efficient Video Representation and Compression by
--   Gaussian Splatting", arXiv:2503.04333v1 (2025).
--
-- This module formalises the paper's representation contract rather than
-- claiming a verified implementation or reproducing its empirical results.
-- A video is represented by time-conditioned deformations of a shared set of
-- 2D Gaussians.  The representation is image-plane and lossy: it is not a 3D
-- scene reconstruction, an exact event record, or a subject identity carrier.

paperTitle : String
paperTitle = "GaussianVideo: Efficient Video Representation and Compression by Gaussian Splatting"

paperAuthors : List String
paperAuthors =
  "Inseo Lee" ∷ "Youngyoon Choi" ∷ "Joonseok Lee" ∷ []

paperReference : String
paperReference = "arXiv:2503.04333v1"

data Never : Set where

data GaussianVideoRoute : Set where
  candidateRepresentationRoute : GaussianVideoRoute
  exactFrameRecoveryRoute : GaussianVideoRoute
  geometryRecoveryRoute : GaussianVideoRoute
  identityRecoveryRoute : GaussianVideoRoute
  evidenceAuthorityRoute : GaussianVideoRoute

AdmissibleGaussianVideoRoute : GaussianVideoRoute → Set
AdmissibleGaussianVideoRoute candidateRepresentationRoute = ⊤
AdmissibleGaussianVideoRoute exactFrameRecoveryRoute = Never
AdmissibleGaussianVideoRoute geometryRecoveryRoute = Never
AdmissibleGaussianVideoRoute identityRecoveryRoute = Never
AdmissibleGaussianVideoRoute evidenceAuthorityRoute = Never

exactFrameRecoveryRejected :
  AdmissibleGaussianVideoRoute exactFrameRecoveryRoute → Never
exactFrameRecoveryRejected impossible = impossible

geometryRecoveryRejected :
  AdmissibleGaussianVideoRoute geometryRecoveryRoute → Never
geometryRecoveryRejected impossible = impossible

identityRecoveryRejected :
  AdmissibleGaussianVideoRoute identityRecoveryRoute → Never
identityRecoveryRejected impossible = impossible

evidenceAuthorityRejected :
  AdmissibleGaussianVideoRoute evidenceAuthorityRoute → Never
evidenceAuthorityRejected impossible = impossible

data GaussianAttributeKind : Set where
  meanAttribute : GaussianAttributeKind
  colourAttribute : GaussianAttributeKind
  rotationAttribute : GaussianAttributeKind
  scaleAttribute : GaussianAttributeKind
  covarianceAttribute : GaussianAttributeKind

data PlaneKind : Set where
  xyPlane : PlaneKind
  xtPlane : PlaneKind
  ytPlane : PlaneKind

data InitializationKind : Set where
  randomInitialization : InitializationKind
  opticalFlowInitialization : InitializationKind
  temporalGradientInitialization : InitializationKind

data LossKind : Set where
  reconstructionLoss : LossKind
  totalVariationLoss : LossKind
  combinedLoss : LossKind

record VideoFrameReceipt : Set where
  constructor mkVideoFrameReceipt
  field
    frameIndex : Nat
    frameWidth : Nat
    frameHeight : Nat
    frameSource : String
    frameIsGroundTruth : Bool
open VideoFrameReceipt public

record Gaussian2DSeed : Set where
  constructor mkGaussian2DSeed
  field
    gaussianIndex : Nat
    meanX : Nat
    meanY : Nat
    covarianceXX : Nat
    covarianceXY : Nat
    covarianceYY : Nat
    baseRed : Nat
    baseGreen : Nat
    baseBlue : Nat
open Gaussian2DSeed public

record TimeConditionedDeformation : Set where
  constructor mkTimeConditionedDeformation
  field
    deformationGaussian : Gaussian2DSeed
    deformationTime : Nat
    deltaMeanX : Nat
    deltaMeanY : Nat
    deltaRotation : Nat
    deltaScaleX : Nat
    deltaScaleY : Nat
    deltaRed : Nat
    deltaGreen : Nat
    deltaBlue : Nat
    deformationPredicted : Bool
    deformationPredictedIsTrue : deformationPredicted ≡ true
open TimeConditionedDeformation public

record MultiPlaneFeatureReceipt : Set where
  constructor mkMultiPlaneFeatureReceipt
  field
    featureGaussianIndex : Nat
    featureTime : Nat
    featurePlanes : List PlaneKind
    featureResolutionLevels : List Nat
    featureUsesHadamardAggregation : Bool
    featureUsesHadamardAggregationIsTrue :
      featureUsesHadamardAggregation ≡ true
open MultiPlaneFeatureReceipt public

record TemporalGradientReceipt : Set where
  constructor mkTemporalGradientReceipt
  field
    gradientFrameA : Nat
    gradientFrameB : Nat
    gradientMagnitude : Nat
    gradientRegion : String
    gradientUsedForAllocation : Bool
    gradientUsedForAllocationIsTrue :
      gradientUsedForAllocation ≡ true
open TemporalGradientReceipt public

record GaussianAllocationReceipt : Set where
  constructor mkGaussianAllocationReceipt
  field
    allocationKind : InitializationKind
    allocationRegion : String
    allocationCount : Nat
    allocationTracksTemporalVariation : Bool
    allocationTracksTemporalVariationIsTrue :
      allocationTracksTemporalVariation ≡ true
open GaussianAllocationReceipt public

record GaussianVideoLossReceipt : Set where
  constructor mkGaussianVideoLossReceipt
  field
    lossKinds : List LossKind
    reconstructionTerm : Nat
    totalVariationTerm : Nat
    totalLoss : Nat
    lossIsMetricProxy : Bool
    lossIsMetricProxyIsTrue : lossIsMetricProxy ≡ true
open GaussianVideoLossReceipt public

record GaussianVideoModelReceipt : Set where
  constructor mkGaussianVideoModelReceipt
  field
    modelName : String
    modelPaper : String
    modelFrames : List VideoFrameReceipt
    modelSeeds : List Gaussian2DSeed
    modelFeatures : List MultiPlaneFeatureReceipt
    modelDeformations : List TimeConditionedDeformation
    modelGradients : List TemporalGradientReceipt
    modelAllocations : List GaussianAllocationReceipt
    modelLosses : List GaussianVideoLossReceipt
    modelQuantizedBits : Nat
    modelCandidateOnly : Bool
    modelCandidateOnlyIsTrue : modelCandidateOnly ≡ true
    modelLossy : Bool
    modelLossyIsTrue : modelLossy ≡ true
    modelRecoversGeometry : Bool
    modelRecoversGeometryIsFalse : modelRecoversGeometry ≡ false
open GaussianVideoModelReceipt public

record GaussianVideoEpisodeBridge : Set where
  constructor mkGaussianVideoEpisodeBridge
  field
    episodeHistory : SpacetimeHistory
    episodeStereo4D : Stereo4DEpisodeReceipt
    episodeVideoModel : GaussianVideoModelReceipt
    episodeLocalTimeStart : Nat
    episodeLocalTimeEnd : Nat
    episodeVisualCarrierOnly : Bool
    episodeVisualCarrierOnlyIsTrue : episodeVisualCarrierOnly ≡ true
    episodeReplacesHistory : Bool
    episodeReplacesHistoryIsFalse : episodeReplacesHistory ≡ false
    episodeReplacesGeometry : Bool
    episodeReplacesGeometryIsFalse : episodeReplacesGeometry ≡ false
open GaussianVideoEpisodeBridge public

mkGaussianVideoModelReceiptOf :
  String →
  List VideoFrameReceipt →
  List Gaussian2DSeed →
  List MultiPlaneFeatureReceipt →
  List TimeConditionedDeformation →
  List TemporalGradientReceipt →
  List GaussianAllocationReceipt →
  List GaussianVideoLossReceipt →
  Nat →
  GaussianVideoModelReceipt
mkGaussianVideoModelReceiptOf name frames seeds features deformations gradients allocations losses bits =
  mkGaussianVideoModelReceipt
    name
    paperReference
    frames
    seeds
    features
    deformations
    gradients
    allocations
    losses
    bits
    true
    refl
    true
    refl
    false
    refl

canonicalGaussianVideoNotes : List String
canonicalGaussianVideoNotes =
  "GaussianVideo represents video with a shared set of deformable 2D Gaussians"
  ∷ "Gaussian attributes are conditioned on time rather than re-created independently per frame"
  ∷ "The encoder factors x-y-t information into xy, xt, and yt planes"
  ∷ "Plane features are aggregated and decoded into mean, colour, rotation, and scale changes"
  ∷ "Temporal gradients allocate more Gaussians to regions with greater temporal variation"
  ∷ "Reconstruction and total-variation losses remain optimization proxies"
  ∷ "The compressed representation is image-plane and does not recover 3D geometry"
  ∷ "A visual episode may decorate a world-tube section but cannot replace the history carrier"
  ∷ "Quantized model state is not an exact archive of every source frame"
  ∷ []
