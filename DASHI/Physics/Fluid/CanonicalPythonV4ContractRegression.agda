module DASHI.Physics.Fluid.CanonicalPythonV4ContractRegression where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Unit using (tt)

open import DASHI.Physics.Fluid.BandedVorticitySpinTwist using (fastMode)
open import DASHI.Physics.Fluid.CanonicalPythonV4Contract

------------------------------------------------------------------------
-- Canonical executable witnesses for the reviewed Python implementation.

canonicalPeriodicFFT : FeatureImplemented periodicFFTGeometry
canonicalPeriodicFFT = tt

canonicalLowModes : FeatureImplemented retainedLowComplexModes
canonicalLowModes = tt

canonicalTopKMidModes : FeatureImplemented retainedTopKMidComplexModes
canonicalTopKMidModes = tt

canonicalResidualEnergy : FeatureImplemented residualBandEnergySummaries
canonicalResidualEnergy = tt

canonicalTernaryMask : FeatureImplemented ternarySupportSignMask
canonicalTernaryMask = tt

canonicalDeterministicSeed : FeatureImplemented deterministicFrameSeed
canonicalDeterministicSeed = tt

canonicalAtomDecodeHook : FeatureImplemented optionalGaussianAtomSplat
canonicalAtomDecodeHook = tt

canonicalReceiptMode : receiptMode canonicalCurrentV4Receipt ≡ fastMode
canonicalReceiptMode = refl

canonicalReceiptHeldOutFalse :
  receiptUsesHeldOutData canonicalCurrentV4Receipt ≡ false
canonicalReceiptHeldOutFalse = refl

canonicalReceiptPeriodicSmootherFalse :
  receiptPeriodicSmoother canonicalCurrentV4Receipt ≡ false
canonicalReceiptPeriodicSmootherFalse = refl

canonicalReceiptHermitianResidualFalse :
  receiptHermitianResidual canonicalCurrentV4Receipt ≡ false
canonicalReceiptHermitianResidualFalse = refl

canonicalReceiptAtomExtractionFalse :
  receiptAtomExtraction canonicalCurrentV4Receipt ≡ false
canonicalReceiptAtomExtractionFalse = refl

canonicalReceiptAtomTransportFalse :
  receiptAtomTransport canonicalCurrentV4Receipt ≡ false
canonicalReceiptAtomTransportFalse = refl

canonicalReceiptPromotedFalse :
  receiptPromoted canonicalCurrentV4Receipt ≡ false
canonicalReceiptPromotedFalse = refl
