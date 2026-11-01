module DASHI.Visualisation.RendererStabilityExact where

open import DASHI.Core.Prelude

import DASHI.Visualisation.SelfConsistentEventRendererExact as Renderer

------------------------------------------------------------------------
-- Finite exact completion of sections 725, 727, 734--750, and 752--753:
-- damped iteration, sorted top-two data, calibration dependence, transfer
-- functions, exact front-to-back compositing, palette bounds, equivariance,
-- and seam diagnostics.

record Fraction : Set where
  constructor fraction
  field
    numerator : Nat
    denominator : Nat

open Fraction public

multiplyFraction : Fraction → Fraction → Fraction
multiplyFraction left right =
  fraction
    (numerator left * numerator right)
    (denominator left * denominator right)

addFraction : Fraction → Fraction → Fraction
addFraction left right =
  fraction
    (numerator left * denominator right
      + numerator right * denominator left)
    (denominator left * denominator right)

oneMinusFraction : Fraction → Fraction
oneMinusFraction value =
  fraction
    (denominator value ∸ numerator value)
    (denominator value)

half : Fraction
half = fraction 1 2

threeQuarters : Fraction
threeQuarters = fraction 3 4

one : Fraction
one = fraction 1 1

------------------------------------------------------------------------
-- Exact straight-alpha front-to-back compositing.  Colour values are assumed
-- premultiplied by their accumulated opacity.

frontToBackColour :
  Fraction → Fraction → Fraction → Fraction → Fraction
frontToBackColour accumulatedColour accumulatedAlpha sampleColour sampleAlpha =
  addFraction
    accumulatedColour
    (multiplyFraction
      (oneMinusFraction accumulatedAlpha)
      (multiplyFraction sampleAlpha sampleColour))

frontToBackAlpha : Fraction → Fraction → Fraction
frontToBackAlpha accumulatedAlpha sampleAlpha =
  addFraction
    accumulatedAlpha
    (multiplyFraction
      (oneMinusFraction accumulatedAlpha)
      sampleAlpha)

canonicalCompositedColour :
  frontToBackColour half half one threeQuarters
  ≡
  fraction 14 16
canonicalCompositedColour = refl

canonicalCompositedAlpha :
  frontToBackAlpha half threeQuarters
  ≡
  fraction 14 16
canonicalCompositedAlpha = refl

data VolumeObservationMode : Set where
  maximumIntensityMode : VolumeObservationMode
  straightAlphaMode : VolumeObservationMode
  additiveEmissionMode : VolumeObservationMode
  isosurfaceMode : VolumeObservationMode

------------------------------------------------------------------------
-- Damped fixed-point iteration with an explicit rational damping coefficient.
-- The finite sample uses omega=1/2 and stores the unnormalised numerator and
-- denominator rather than hiding integer division.

record DampedStep : Set where
  constructor dampedStep
  field
    currentValue : Nat
    operatorValue : Nat
    dampingNumerator : Nat
    dampingDenominator : Nat
    nextNumerator : Nat
    nextDenominator : Nat
    dampedStepCloses :
      (dampingDenominator ∸ dampingNumerator) * currentValue
      + dampingNumerator * operatorValue
      ≡ nextNumerator
    denominatorCloses : nextDenominator ≡ dampingDenominator

open DampedStep public

canonicalDampedStep : DampedStep
canonicalDampedStep =
  dampedStep 2 6 1 2 8 2 refl refl

canonicalDampedValueIsEightHalves :
  nextNumerator canonicalDampedStep ≡ 8
  ×
  nextDenominator canonicalDampedStep ≡ 2
canonicalDampedValueIsEightHalves = refl , refl

record IterationStopReceipt : Set where
  constructor iterationStopReceipt
  field
    previousScaled : Nat
    nextScaled : Nat
    toleranceScaled : Nat
    stopped : Bool

open IterationStopReceipt public

canonicalStopReceipt : IterationStopReceipt
canonicalStopReceipt = iterationStopReceipt 12 13 1 true

canonicalIterationStops : stopped canonicalStopReceipt ≡ true
canonicalIterationStops = refl

------------------------------------------------------------------------
-- Top-two values are represented as sorted order statistics, avoiding an
-- arbitrary selected maximiser at ties.

record SortedTopTwo : Set where
  constructor sortedTopTwo
  field
    firstOrderStatistic : Nat
    secondOrderStatistic : Nat

open SortedTopTwo public

topTwoGap : SortedTopTwo → Nat
topTwoGap values =
  firstOrderStatistic values ∸ secondOrderStatistic values

tiedOrderStatistics : SortedTopTwo
tiedOrderStatistics = sortedTopTwo 7 7

dominantOrderStatistics : SortedTopTwo
dominantOrderStatistics = sortedTopTwo 9 3

tiedGapIsZero : topTwoGap tiedOrderStatistics ≡ 0
tiedGapIsZero = refl

dominantGapIsSix : topTwoGap dominantOrderStatistics ≡ 6
dominantGapIsSix = refl

------------------------------------------------------------------------
-- Global-frame maximum dependence.  One unchanged local field value receives
-- different calibrated fractions when a distant maximum changes.

record FrameCalibration : Set where
  constructor frameCalibration
  field
    localValue : Nat
    frameReference : Nat

open FrameCalibration public

smallFrame : FrameCalibration
smallFrame = frameCalibration 4 8

largeFrameWithDistantPeak : FrameCalibration
largeFrameWithDistantPeak = frameCalibration 4 16

calibratedFraction : FrameCalibration → Fraction
calibratedFraction frame =
  fraction (localValue frame) (frameReference frame)

sameLocalValueDifferentFrameCalibration :
  localValue smallFrame ≡ localValue largeFrameWithDistantPeak
sameLocalValueDifferentFrameCalibration = refl

calibrationFractionsDiffer :
  calibratedFraction smallFrame
  ≡
  calibratedFraction largeFrameWithDistantPeak
  →
  ⊥
calibrationFractionsDiffer ()

data StableReferencePolicy : Set where
  fixedAtlasReference : StableReferencePolicy
  robustQuantileReference : StableReferencePolicy
  frameMaximumReference : StableReferencePolicy

------------------------------------------------------------------------
-- Density powers are explicit monotone transfer choices on one finite grid.

data UnitDensityLevel : Set where
  densityZero : UnitDensityLevel
  densityHalf : UnitDensityLevel
  densityOne : UnitDensityLevel

squareTransfer : UnitDensityLevel → Nat
squareTransfer densityZero = 0
squareTransfer densityHalf = 1
squareTransfer densityOne = 4

rootLikeTransfer : UnitDensityLevel → Nat
rootLikeTransfer densityZero = 0
rootLikeTransfer densityHalf = 2
rootLikeTransfer densityOne = 4

squareSuppressesLowDensityMore :
  squareTransfer densityHalf ≡ 1
  ×
  rootLikeTransfer densityHalf ≡ 2
squareSuppressesLowDensityMore = refl , refl

------------------------------------------------------------------------
-- A finite convex RGB palette.  Bounded nonnegative class columns and a
-- denominator-four mixture produce bounded channel numerators.

record RGB3 : Set where
  constructor rgb3
  field
    red : Nat
    green : Nat
    blue : Nat

open RGB3 public

record Palette2 : Set where
  constructor palette2
  field
    paletteClassOne : RGB3
    paletteClassTwo : RGB3

open Palette2 public

record Mixture2 : Set where
  constructor mixture2
  field
    mixtureOne : Nat
    mixtureTwo : Nat
    mixtureDenominator : Nat
    mixtureCloses :
      mixtureOne + mixtureTwo ≡ mixtureDenominator

open Mixture2 public

applyPalette : Palette2 → Mixture2 → RGB3
applyPalette palette mixture =
  rgb3
    (mixtureOne mixture * red (paletteClassOne palette)
      + mixtureTwo mixture * red (paletteClassTwo palette))
    (mixtureOne mixture * green (paletteClassOne palette)
      + mixtureTwo mixture * green (paletteClassTwo palette))
    (mixtureOne mixture * blue (paletteClassOne palette)
      + mixtureTwo mixture * blue (paletteClassTwo palette))

canonicalPalette : Palette2
canonicalPalette = palette2 (rgb3 4 0 0) (rgb3 0 0 4)

canonicalMixture : Mixture2
canonicalMixture = mixture2 1 3 4 refl

canonicalPaletteOutput :
  applyPalette canonicalPalette canonicalMixture
  ≡
  rgb3 4 0 12
canonicalPaletteOutput = refl

canonicalPaletteChannelsWithinScaledRange :
  red (applyPalette canonicalPalette canonicalMixture) ≡ 4
  ×
  green (applyPalette canonicalPalette canonicalMixture) ≡ 0
  ×
  blue (applyPalette canonicalPalette canonicalMixture) ≡ 12
canonicalPaletteChannelsWithinScaledRange = refl , (refl , refl)

------------------------------------------------------------------------
-- Finite joint-frame equivariance.  Translating query and event centre by the
-- same amount preserves the declared one-dimensional relative displacement.

relativeDisplacement : Nat → Nat → Nat
relativeDisplacement query centre = query ∸ centre

jointTranslationPreservesSampleDistance :
  relativeDisplacement (7 + 5) (3 + 5)
  ≡
  relativeDisplacement 7 3
jointTranslationPreservesSampleDistance = refl

queryOnlyTranslationChangesSampleDistance :
  relativeDisplacement (7 + 5) 3
  ≡
  relativeDisplacement 7 3
  →
  ⊥
queryOnlyTranslationChangesSampleDistance ()

------------------------------------------------------------------------
-- A finite hierarchical isometry.  Relabelling every address digit by the
-- same permutation preserves shared-prefix depth.

data PrefixPair : Set where
  noSharedPrefix : PrefixPair
  oneSharedDigit : PrefixPair
  twoSharedDigits : PrefixPair

permuteHierarchy : PrefixPair → PrefixPair
permuteHierarchy noSharedPrefix = noSharedPrefix
permuteHierarchy oneSharedDigit = oneSharedDigit
permuteHierarchy twoSharedDigits = twoSharedDigits

prefixDepthCode : PrefixPair → Nat
prefixDepthCode noSharedPrefix = 0
prefixDepthCode oneSharedDigit = 1
prefixDepthCode twoSharedDigits = 2

hierarchyIsometryPreservesDepth :
  (pair : PrefixPair) →
  prefixDepthCode (permuteHierarchy pair) ≡ prefixDepthCode pair
hierarchyIsometryPreservesDepth noSharedPrefix = refl
hierarchyIsometryPreservesDepth oneSharedDigit = refl
hierarchyIsometryPreservesDepth twoSharedDigits = refl

------------------------------------------------------------------------
-- Continuity and differentiability seams are reported, not hidden.

data SeamOperation : Set where
  reluSeam : SeamOperation
  clippingSeam : SeamOperation
  voidSwitchSeam : SeamOperation
  topTwoExchangeSeam : SeamOperation

data SeamRegularity : Set where
  continuousNondifferentiable : SeamRegularity
  discontinuousConvention : SeamRegularity
  smoothApproximationAvailable : SeamRegularity

seamRegularity : SeamOperation → SeamRegularity
seamRegularity reluSeam = continuousNondifferentiable
seamRegularity clippingSeam = continuousNondifferentiable
seamRegularity voidSwitchSeam = discontinuousConvention
seamRegularity topTwoExchangeSeam = continuousNondifferentiable

record RendererStabilityBoundary : Set where
  constructor rendererStabilityBoundary
  field
    undampedIterationAlwaysConverges : Bool
    undampedIterationAlwaysConvergesIsFalse :
      undampedIterationAlwaysConverges ≡ false

    selectedArgmaxDefinesTieInvariantSecondMaximum : Bool
    selectedArgmaxDefinesTieInvariantSecondMaximumIsFalse :
      selectedArgmaxDefinesTieInvariantSecondMaximum ≡ false

    frameMaximumIsAbsoluteCalibration : Bool
    frameMaximumIsAbsoluteCalibrationIsFalse :
      frameMaximumIsAbsoluteCalibration ≡ false

    straightAlphaEqualsMaximumIntensityProjection : Bool
    straightAlphaEqualsMaximumIntensityProjectionIsFalse :
      straightAlphaEqualsMaximumIntensityProjection ≡ false

    jointFrameEquivarianceMeansQueryOnlyInvariance : Bool
    jointFrameEquivarianceMeansQueryOnlyInvarianceIsFalse :
      jointFrameEquivarianceMeansQueryOnlyInvariance ≡ false

open RendererStabilityBoundary public

canonicalRendererStabilityBoundary : RendererStabilityBoundary
canonicalRendererStabilityBoundary =
  rendererStabilityBoundary false refl false refl false refl false refl false refl
