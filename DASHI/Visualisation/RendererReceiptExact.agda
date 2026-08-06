module DASHI.Visualisation.RendererReceiptExact where

open import DASHI.Core.Prelude

import DASHI.Visualisation.RendererParityExact as Parity

------------------------------------------------------------------------
-- Every semantic renderer stage is named so stage-level differential testing
-- cannot be replaced by one composite screenshot.

data RendererStage : Set where
  sliceStage : RendererStage
  distanceStage : RendererStage
  activationStage : RendererStage
  topTwoStage : RendererStage
  ambiguityStage : RendererStage
  colourStage : RendererStage
  activityStage : RendererStage
  encodingStage : RendererStage

data NumericDType : Set where
  float32Type : NumericDType
  float64Type : NumericDType
  int8Type : NumericDType
  int32Type : NumericDType

data ColourMode : Set where
  cmykMode : ColourMode
  pcaMode : ColourMode
  fixedPaletteMode : ColourMode

data AlphaConvention : Set where
  noAlpha : AlphaConvention
  straightAlpha : AlphaConvention
  premultipliedAlpha : AlphaConvention

record RendererConfiguration : Set where
  constructor rendererConfiguration
  field
    ambientDimension : Nat
    classCount : Nat
    gridWidth : Nat
    gridHeight : Nat
    sharpnessScale : Nat
    ambiguityStrength : Nat
    colourMode : ColourMode
    alphaConvention : AlphaConvention
    fieldDType : NumericDType
    accumulationDType : NumericDType
    fixedSeed : Nat

open RendererConfiguration public

canonicalRendererConfiguration : RendererConfiguration
canonicalRendererConfiguration =
  rendererConfiguration
    4 5 64 64 3 2
    cmykMode noAlpha float32Type float64Type 369

configurationDimensionIsFour :
  ambientDimension canonicalRendererConfiguration ≡ 4
configurationDimensionIsFour = refl

data FeatureFlag : Set where
  quadraticDistanceFlag : FeatureFlag
  streamingTopTwoFlag : FeatureFlag
  alphaOutputFlag : FeatureFlag
  int8SearchFlag : FeatureFlag

data FlagState : Set where
  flagDisabled : FlagState
  flagEnabled : FlagState

referenceFlagState : FeatureFlag → FlagState
referenceFlagState _ = flagDisabled

quadraticOnlyFlagState : FeatureFlag → FlagState
quadraticOnlyFlagState quadraticDistanceFlag = flagEnabled
quadraticOnlyFlagState _ = flagDisabled

quadraticFlagIsEnabled :
  quadraticOnlyFlagState quadraticDistanceFlag ≡ flagEnabled
quadraticFlagIsEnabled = refl

int8FlagRemainsDisabledInParityPath :
  quadraticOnlyFlagState int8SearchFlag ≡ flagDisabled
int8FlagRemainsDisabledInParityPath = refl

------------------------------------------------------------------------
-- Buffer-level parity.  Distances, activations, RGB floats, and encoded pixels
-- are not interchangeable evidence.

data BufferLevel : Set where
  distanceBuffer : BufferLevel
  activationBuffer : BufferLevel
  ambiguityBuffer : BufferLevel
  floatRGBBuffer : BufferLevel
  encodedPixelBuffer : BufferLevel

record BufferDifference : Set where
  constructor bufferDifference
  field
    bufferLevel : BufferLevel
    maximumErrorScaled : Nat
    meanSquaredErrorScaled : Nat

open BufferDifference public

exactDistanceDifference : BufferDifference
exactDistanceDifference =
  bufferDifference distanceBuffer 0 0

exactFloatRGBDifference : BufferDifference
exactFloatRGBDifference =
  bufferDifference floatRGBBuffer 0 0

encodedToleranceDifference : BufferDifference
encodedToleranceDifference =
  bufferDifference encodedPixelBuffer 1 1

distanceParityIsExact :
  maximumErrorScaled exactDistanceDifference ≡ 0
distanceParityIsExact = refl

------------------------------------------------------------------------
-- Property-test catalogue.

data RendererProperty : Set where
  outputRangeProperty : RendererProperty
  zeroActivityProperty : RendererProperty
  tiePermutationProperty : RendererProperty
  sliceReparameterisationProperty : RendererProperty
  declaredSymmetryProperty : RendererProperty

data PropertyStatus : Set where
  propertyChecked : PropertyStatus
  propertyPending : PropertyStatus

canonicalPropertyStatus : RendererProperty → PropertyStatus
canonicalPropertyStatus outputRangeProperty = propertyChecked
canonicalPropertyStatus zeroActivityProperty = propertyChecked
canonicalPropertyStatus tiePermutationProperty = propertyChecked
canonicalPropertyStatus sliceReparameterisationProperty = propertyChecked
canonicalPropertyStatus declaredSymmetryProperty = propertyPending

slicePropertyIsChecked :
  canonicalPropertyStatus sliceReparameterisationProperty
  ≡
  propertyChecked
slicePropertyIsChecked = refl

------------------------------------------------------------------------
-- Benchmark protocol and performance data are explicit declarations.  The
-- presence of a record does not assert that a benchmark has actually run.

record TimingProtocol : Set where
  constructor timingProtocol
  field
    warmupRuns : Nat
    measuredRuns : Nat
    threadCount : Nat
    importTimeExcluded : Bool
    sameConfigurationUsed : Bool

open TimingProtocol public

canonicalTimingProtocol : TimingProtocol
canonicalTimingProtocol =
  timingProtocol 3 11 1 true true

record PerformanceSummary : Set where
  constructor performanceSummary
  field
    referenceMedianTicks : Nat
    vanillaMedianTicks : Nat
    optimisedMedianTicks : Nat
    dispersionTicks : Nat

open PerformanceSummary public

illustrativePerformanceSummary : PerformanceSummary
illustrativePerformanceSummary =
  performanceSummary 120 118 60 4

illustrativeSpeedupNumerator : Nat
illustrativeSpeedupNumerator =
  referenceMedianTicks illustrativePerformanceSummary

illustrativeSpeedupDenominator : Nat
illustrativeSpeedupDenominator =
  optimisedMedianTicks illustrativePerformanceSummary

illustrativeTwofoldRatio :
  illustrativeSpeedupNumerator
  ≡
  2 * illustrativeSpeedupDenominator
illustrativeTwofoldRatio = refl

------------------------------------------------------------------------
-- Receipt hierarchy.  P4 requires an algebraic equality witness plus a
-- separately declared numerical/error and execution surface.

record RendererReceipt : Set where
  constructor rendererReceipt
  field
    level : Parity.ParityLevel
    referenceCommitHash : Nat
    candidateCommitHash : Nat
    configurationHash : Nat
    configuration : RendererConfiguration
    distanceDifference : BufferDifference
    rgbDifference : BufferDifference
    encodedDifference : BufferDifference
    bitwiseFloatEqual : Bool
    receiptTimingProtocol : TimingProtocol
    receiptPerformanceSummary : PerformanceSummary
    benchmarkExecuted : Bool
    ciKernelCheckSucceeded : Bool

open RendererReceipt public

canonicalSourceReceipt : RendererReceipt
canonicalSourceReceipt =
  rendererReceipt
    Parity.algebraicParityP4
    401
    670
    369
    canonicalRendererConfiguration
    exactDistanceDifference
    exactFloatRGBDifference
    encodedToleranceDifference
    true
    canonicalTimingProtocol
    illustrativePerformanceSummary
    false
    false

sourceReceiptHasP4Declaration :
  level canonicalSourceReceipt ≡ Parity.algebraicParityP4
sourceReceiptHasP4Declaration = refl

sourceReceiptDoesNotClaimExecutedBenchmark :
  benchmarkExecuted canonicalSourceReceipt ≡ false
sourceReceiptDoesNotClaimExecutedBenchmark = refl

sourceReceiptDoesNotClaimKernelCI :
  ciKernelCheckSucceeded canonicalSourceReceipt ≡ false
sourceReceiptDoesNotClaimKernelCI = refl

record RendererReceiptBoundary : Set where
  constructor rendererReceiptBoundary
  field
    identicalEncodedPixelsProveIdenticalActivationBuffers : Bool
    identicalEncodedPixelsProveIdenticalActivationBuffersIsFalse :
      identicalEncodedPixelsProveIdenticalActivationBuffers ≡ false

    oneReferenceConfigurationProvesUniversalParity : Bool
    oneReferenceConfigurationProvesUniversalParityIsFalse :
      oneReferenceConfigurationProvesUniversalParity ≡ false

    declaredTimingRecordIsExecutedBenchmark : Bool
    declaredTimingRecordIsExecutedBenchmarkIsFalse :
      declaredTimingRecordIsExecutedBenchmark ≡ false

    p4SourceDeclarationIsReproducibleCIReceipt : Bool
    p4SourceDeclarationIsReproducibleCIReceiptIsFalse :
      p4SourceDeclarationIsReproducibleCIReceipt ≡ false

open RendererReceiptBoundary public

canonicalRendererReceiptBoundary : RendererReceiptBoundary
canonicalRendererReceiptBoundary =
  rendererReceiptBoundary
    false refl
    false refl
    false refl
    false refl
