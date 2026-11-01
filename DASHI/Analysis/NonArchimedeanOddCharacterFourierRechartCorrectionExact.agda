module DASHI.Analysis.NonArchimedeanOddCharacterFourierRechartCorrectionExact where

------------------------------------------------------------------------
-- ODD-CHARACTER FOURIER RECHART CORRECTION
--
-- The literal twisted block is indexed by the antisymmetric sheet coordinate
-- v : ZMod(2^(n-1)).  Source `Analysis/DFT.lean` then applies an arbitrary
-- cardinality reindex
--
--   ZMod(2^(n-1)) ~= ZMod(2^(n-2)) x ZMod 2
--
-- followed by F_(2^(n-2)) tensor I_2.
--
-- That construction is a valid unitary carrier transform, but it is not by
-- itself the Pontryagin odd-character basis of ZMod(2^n).
--
-- If omega has order 2^n, every odd frequency is k = 2j+1 and
--
--   omega^((2j+1)v) = omega^v * (omega^2)^(jv).
--
-- Hence the natural antisymmetric/odd-character transform is a modulated
-- 2^(n-1)-point DFT using omega^2, not an arbitrary product reindex followed
-- by F_(2^(n-2)) tensor I_2.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)

record OddCharacterFourierRechart : Set₁ where
  field
    SpatialHalfIndex : Set
    OddFrequencyIndex : Set
    Scalar : Set

    spatialToOddFrequency : SpatialHalfIndex → OddFrequencyIndex
    oddFrequencyToSpatial : OddFrequencyIndex → SpatialHalfIndex

    spatialRoundTrip :
      (v : SpatialHalfIndex) →
      oddFrequencyToSpatial (spatialToOddFrequency v) ≡ v

    frequencyRoundTrip :
      (k : OddFrequencyIndex) →
      spatialToOddFrequency (oddFrequencyToSpatial k) ≡ k

    ordinaryHalfDFTKernel :
      SpatialHalfIndex → SpatialHalfIndex → Scalar

    modulation : SpatialHalfIndex → Scalar

    oddCharacterKernel :
      OddFrequencyIndex → SpatialHalfIndex → Scalar

    oddKernelFactorsAsModulatedHalfDFT :
      (k : OddFrequencyIndex) (v : SpatialHalfIndex) → Set

open OddCharacterFourierRechart public

record SourceDFTComparison : Set where
  constructor sourceDFTComparison
  field
    currentCardinalityProductReindexOwned : Bool
    currentFTensorIdentityUnitarityOwned : Bool
    currentTransformUsesOrderTwoPowNMinusTwoRoot : Bool
    currentTransformDefinitionallyEqualsOddCharacterTransform : Bool

    oddCharacterTransformNeedsOrderTwoPowNRoot : Bool
    oddCharacterTransformUsesSquaredRootAtHalfSize : Bool
    oddCharacterTransformNeedsModulation : Bool

canonicalSourceDFTComparison : SourceDFTComparison
canonicalSourceDFTComparison =
  sourceDFTComparison
    true true true false
    true true true


data FourierRechartLeaf : Set where
  instantiatePrimitiveTwoPowNRoot : FourierRechartLeaf
  deriveSquaredRootPrimitiveAtHalfSize : FourierRechartLeaf
  defineOddFrequencyParameterization : FourierRechartLeaf
  defineHalfSizeDFT : FourierRechartLeaf
  defineOddModulation : FourierRechartLeaf
  proveOddKernelFactorization : FourierRechartLeaf
  compileOddCharacterBasisEquivalence : FourierRechartLeaf
  reuseCurrentProductDFTAsOddCharacterBasis : FourierRechartLeaf


data FourierRechartDisposition : Set where
  live : FourierRechartDisposition
  downstream : FourierRechartDisposition
  reusable : FourierRechartDisposition
  forbiddenShortcut : FourierRechartDisposition

fourierRechartDisposition : FourierRechartLeaf → FourierRechartDisposition
fourierRechartDisposition instantiatePrimitiveTwoPowNRoot = live
fourierRechartDisposition deriveSquaredRootPrimitiveAtHalfSize = reusable
fourierRechartDisposition defineOddFrequencyParameterization = live
fourierRechartDisposition defineHalfSizeDFT = reusable
fourierRechartDisposition defineOddModulation = live
fourierRechartDisposition proveOddKernelFactorization = live
fourierRechartDisposition compileOddCharacterBasisEquivalence = downstream
fourierRechartDisposition reuseCurrentProductDFTAsOddCharacterBasis = forbiddenShortcut

highestAlphaOddFourierPath : List FourierRechartLeaf
highestAlphaOddFourierPath =
  instantiatePrimitiveTwoPowNRoot ∷
  defineOddFrequencyParameterization ∷
  defineOddModulation ∷
  proveOddKernelFactorization ∷
  compileOddCharacterBasisEquivalence ∷
  []

record RechartFirewall : Set where
  constructor rechartFirewall
  field
    equalDimensionImpliesSameFourierBasis : Bool
    unitaryTransformImpliesCorrectCharacterSemantics : Bool
    arbitraryProductReindexImpliesOrbitCoordinates : Bool
    modulatedHalfDFTMatchesOddCharacterFormula : Bool

canonicalRechartFirewall : RechartFirewall
canonicalRechartFirewall =
  rechartFirewall false false false true

currentProductDFTNotYetOddCharacterWeld :
  SourceDFTComparison.currentTransformDefinitionallyEqualsOddCharacterTransform
    canonicalSourceDFTComparison
  ≡ false
currentProductDFTNotYetOddCharacterWeld = refl
