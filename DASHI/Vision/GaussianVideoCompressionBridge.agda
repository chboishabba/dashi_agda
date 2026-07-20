module DASHI.Vision.GaussianVideoCompressionBridge where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

open import DASHI.Geometry.SpacetimeHistoryScaleHierarchy
open import DASHI.Vision.Stereo4DDynamicReconstructionBridge
  using (DynamicReconstruction)

------------------------------------------------------------------------
-- Credit: Inseo Lee, Youngyoon Choi, and Joonseok Lee,
-- "GaussianVideo: Efficient Video Representation and Compression by
-- Gaussian Splatting", arXiv:2503.04333v1 (2025).

paperReference : String
paperReference = "Lee, Choi, and Lee, GaussianVideo, arXiv:2503.04333v1 (2025)"

data PlaneKind : Set where
  xyPlane : PlaneKind
  xtPlane : PlaneKind
  ytPlane : PlaneKind

data LossKind : Set where
  reconstructionLoss : LossKind
  totalVariationLoss : LossKind

record Gaussian2DSeed : Set where
  constructor gaussian2DSeed
  field gaussianIndex : Nat
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
  constructor timeConditionedDeformation
  field deformationSeed : Gaussian2DSeed
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

record MultiPlaneFeature : Set where
  constructor multiPlaneFeature
  field featureGaussian : Nat
        featureTime : Nat
        featurePlanes : List PlaneKind
        featureResolutionLevels : List Nat
        hadamardAggregated : Bool
        hadamardAggregatedIsTrue : hadamardAggregated ≡ true
open MultiPlaneFeature public

record TemporalGradientAllocation : Set where
  constructor temporalGradientAllocation
  field gradientRegion : String
        gradientMagnitude : Nat
        allocatedGaussians : Nat
        tracksTemporalVariation : Bool
        tracksTemporalVariationIsTrue : tracksTemporalVariation ≡ true
open TemporalGradientAllocation public

record GaussianVideoLoss : Set where
  constructor gaussianVideoLoss
  field lossKinds : List LossKind
        reconstructionTerm : Nat
        totalVariationTerm : Nat
        totalLoss : Nat
        optimizationProxy : Bool
        optimizationProxyIsTrue : optimizationProxy ≡ true
open GaussianVideoLoss public

record GaussianVideoModel : Set where
  constructor gaussianVideoModel
  field modelName : String
        modelCitation : String
        modelSeeds : List Gaussian2DSeed
        modelFeatures : List MultiPlaneFeature
        modelDeformations : List TimeConditionedDeformation
        modelAllocations : List TemporalGradientAllocation
        modelLosses : List GaussianVideoLoss
        quantizedBits : Nat
        lossy : Bool
        lossyIsTrue : lossy ≡ true
        recoversGeometry : Bool
        recoversGeometryIsFalse : recoversGeometry ≡ false
        physicalMotionAuthority : Bool
        physicalMotionAuthorityIsFalse : physicalMotionAuthority ≡ false
open GaussianVideoModel public

mkCandidateGaussianVideoModel :
  String → List Gaussian2DSeed → List MultiPlaneFeature →
  List TimeConditionedDeformation → List TemporalGradientAllocation →
  List GaussianVideoLoss → Nat → GaussianVideoModel
mkCandidateGaussianVideoModel name seeds features deformations allocations losses bits =
  gaussianVideoModel name paperReference seeds features deformations allocations losses bits
    true refl false refl false refl

record GaussianVideoEpisodeBridge : Set where
  constructor gaussianVideoEpisodeBridge
  field episodeHistory : LongitudinalHistory
        episodeDynamicScene : DynamicReconstruction
        episodeVideoModel : GaussianVideoModel
        visualCarrierOnly : Bool
        visualCarrierOnlyIsTrue : visualCarrierOnly ≡ true
        replacesHistory : Bool
        replacesHistoryIsFalse : replacesHistory ≡ false
        replacesGeometry : Bool
        replacesGeometryIsFalse : replacesGeometry ≡ false
open GaussianVideoEpisodeBridge public

canonicalGaussianVideoNotes : List String
canonicalGaussianVideoNotes =
  "Shared 2D Gaussian seeds are deformed as a function of time"
  ∷ "xy, xt, and yt planes factor the x-y-t representation"
  ∷ "Temporal gradients steer representational allocation"
  ∷ "Reconstruction and total variation are optimization proxies"
  ∷ "Image-plane Gaussian deformation is not world-space physical motion"
  ∷ []
