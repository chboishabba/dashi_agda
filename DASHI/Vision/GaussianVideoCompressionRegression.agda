module DASHI.Vision.GaussianVideoCompressionRegression where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)

open import DASHI.Vision.GaussianVideoCompressionBridge

canonicalFrame : VideoFrameReceipt
canonicalFrame =
  mkVideoFrameReceipt 0 1280 640 "source-frame-0" true

canonicalSeed : Gaussian2DSeed
canonicalSeed =
  mkGaussian2DSeed 0 640 320 1 0 1 255 255 255

canonicalFeature : MultiPlaneFeatureReceipt
canonicalFeature =
  mkMultiPlaneFeatureReceipt
    0
    0
    (xyPlane ∷ xtPlane ∷ ytPlane ∷ [])
    (1 ∷ 2 ∷ [])
    true
    refl

canonicalDeformation : TimeConditionedDeformation
canonicalDeformation =
  mkTimeConditionedDeformation
    canonicalSeed
    0
    0 0 0 0 0 0 0 0
    true
    refl

canonicalGradient : TemporalGradientReceipt
canonicalGradient =
  mkTemporalGradientReceipt 0 1 12 "dynamic-region" true refl

canonicalAllocation : GaussianAllocationReceipt
canonicalAllocation =
  mkGaussianAllocationReceipt
    temporalGradientInitialization
    "dynamic-region"
    64
    true
    refl

canonicalLoss : GaussianVideoLossReceipt
canonicalLoss =
  mkGaussianVideoLossReceipt
    (reconstructionLoss ∷ totalVariationLoss ∷ combinedLoss ∷ [])
    10
    2
    12
    true
    refl

canonicalModel : GaussianVideoModelReceipt
canonicalModel =
  mkGaussianVideoModelReceiptOf
    "canonical GaussianVideo receipt"
    (canonicalFrame ∷ [])
    (canonicalSeed ∷ [])
    (canonicalFeature ∷ [])
    (canonicalDeformation ∷ [])
    (canonicalGradient ∷ [])
    (canonicalAllocation ∷ [])
    (canonicalLoss ∷ [])
    8

candidate-only-regression :
  modelCandidateOnly canonicalModel ≡ true
candidate-only-regression = refl

lossy-regression :
  modelLossy canonicalModel ≡ true
lossy-regression = refl

no-geometry-recovery-regression :
  modelRecoversGeometry canonicalModel ≡ false
no-geometry-recovery-regression = refl

multi-plane-regression :
  featureUsesHadamardAggregation canonicalFeature ≡ true
multi-plane-regression = refl

temporal-gradient-allocation-regression :
  allocationTracksTemporalVariation canonicalAllocation ≡ true
temporal-gradient-allocation-regression = refl

deformation-is-predicted-regression :
  deformationPredicted canonicalDeformation ≡ true
deformation-is-predicted-regression = refl

loss-is-proxy-regression :
  lossIsOptimizationProxy canonicalLoss ≡ true
loss-is-proxy-regression = refl
