module DASHI.Visualisation.EventSeparationQuantisationExact where

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- Exact finite completion of sections 673, 680--681, and 703--704: robust
-- neighbourhood separation with an explicit empty fallback, external-time and
-- enlarged-space product kernels, and componentwise event-parameter error.

data DistanceLevel : Set where
  distanceNear : DistanceLevel
  distanceMiddle : DistanceLevel
  distanceFar : DistanceLevel

levelCode : DistanceLevel → Nat
levelCode distanceNear = 1
levelCode distanceMiddle = 3
levelCode distanceFar = 7

minLevel : DistanceLevel → DistanceLevel → DistanceLevel
minLevel distanceNear _ = distanceNear
minLevel distanceMiddle distanceNear = distanceNear
minLevel distanceMiddle _ = distanceMiddle
minLevel distanceFar other = other

maxLevel : DistanceLevel → DistanceLevel → DistanceLevel
maxLevel distanceFar _ = distanceFar
maxLevel distanceMiddle distanceFar = distanceFar
maxLevel distanceMiddle _ = distanceMiddle
maxLevel distanceNear other = other

medianThree : DistanceLevel → DistanceLevel → DistanceLevel → DistanceLevel
medianThree a b c =
  maxLevel
    (minLevel a b)
    (minLevel (maxLevel a b) c)

medianIgnoresOneFarOutlier :
  medianThree distanceNear distanceMiddle distanceFar
  ≡
  distanceMiddle
medianIgnoresOneFarOutlier = refl

medianOfTwoNearOneFarIsNear :
  medianThree distanceNear distanceFar distanceNear
  ≡
  distanceNear
medianOfTwoNearOneFarIsNear = refl

data ComparisonNeighbourhood : Set where
  emptyNeighbourhood : ComparisonNeighbourhood
  singletonNeighbourhood : DistanceLevel → ComparisonNeighbourhood
  tripleNeighbourhood :
    DistanceLevel → DistanceLevel → DistanceLevel →
    ComparisonNeighbourhood

fallbackSeparation : DistanceLevel
fallbackSeparation = distanceMiddle

localSeparation : ComparisonNeighbourhood → DistanceLevel
localSeparation emptyNeighbourhood = fallbackSeparation
localSeparation (singletonNeighbourhood distance) = distance
localSeparation (tripleNeighbourhood a b c) = medianThree a b c

emptyNeighbourhoodUsesDeclaredFallback :
  localSeparation emptyNeighbourhood ≡ distanceMiddle
emptyNeighbourhoodUsesDeclaredFallback = refl

sharpnessFromSeparation : ComparisonNeighbourhood → Nat
sharpnessFromSeparation neighbourhood =
  levelCode (localSeparation neighbourhood)

outlierRobustSharpness :
  sharpnessFromSeparation
    (tripleNeighbourhood distanceNear distanceMiddle distanceFar)
  ≡
  3
outlierRobustSharpness = refl

------------------------------------------------------------------------
-- External-time product field.  A block-diagonal enlarged-space kernel and an
-- explicitly factored semantic/time kernel have the same finite contribution.

record SemanticTimeKernel : Set where
  constructor semanticTimeKernel
  field
    semanticKernelValue : Nat
    temporalKernelValue : Nat
    sourceWeight : Nat

open SemanticTimeKernel public

externalTimeContribution : SemanticTimeKernel → Nat
externalTimeContribution sample =
  sourceWeight sample
  * semanticKernelValue sample
  * temporalKernelValue sample

blockDiagonalJointContribution : SemanticTimeKernel → Nat
blockDiagonalJointContribution sample =
  sourceWeight sample
  * (semanticKernelValue sample * temporalKernelValue sample)

canonicalSemanticTimeKernel : SemanticTimeKernel
canonicalSemanticTimeKernel = semanticTimeKernel 3 2 5

externalAndJointProductAgree :
  externalTimeContribution canonicalSemanticTimeKernel
  ≡
  blockDiagonalJointContribution canonicalSemanticTimeKernel
externalAndJointProductAgree = refl

canonicalTimedContributionIsThirty :
  externalTimeContribution canonicalSemanticTimeKernel ≡ 30
canonicalTimedContributionIsThirty = refl

data TimePlacement : Set where
  timeInsideAmbientCoordinate : TimePlacement
  timeExternalParameter : TimePlacement

------------------------------------------------------------------------
-- Componentwise event quantisation.  Exact parameter values and stored values
-- remain separate; a declared sensitivity budget converts component errors to
-- a field-error upper code.

record EventParameterTuple : Set where
  constructor eventParameterTuple
  field
    parameterCentre : Nat
    parameterScale : Nat
    parameterWeight : Nat
    parameterSharpness : Nat

open EventParameterTuple public

exactParameters : EventParameterTuple
exactParameters = eventParameterTuple 10 8 6 4

quantisedParameters : EventParameterTuple
quantisedParameters = eventParameterTuple 9 7 6 3

absoluteDifference : Nat → Nat → Nat
absoluteDifference a b = (a ∸ b) + (b ∸ a)

record ParameterErrorTuple : Set where
  constructor parameterErrorTuple
  field
    centreError : Nat
    scaleError : Nat
    weightError : Nat
    sharpnessError : Nat

open ParameterErrorTuple public

parameterError : EventParameterTuple → EventParameterTuple → ParameterErrorTuple
parameterError exact stored =
  parameterErrorTuple
    (absoluteDifference
      (parameterCentre exact)
      (parameterCentre stored))
    (absoluteDifference
      (parameterScale exact)
      (parameterScale stored))
    (absoluteDifference
      (parameterWeight exact)
      (parameterWeight stored))
    (absoluteDifference
      (parameterSharpness exact)
      (parameterSharpness stored))

canonicalParameterError :
  parameterError exactParameters quantisedParameters
  ≡
  parameterErrorTuple 1 1 0 1
canonicalParameterError = refl

record SensitivityTuple : Set where
  constructor sensitivityTuple
  field
    centreSensitivity : Nat
    scaleSensitivity : Nat
    weightSensitivity : Nat
    sharpnessSensitivity : Nat

open SensitivityTuple public

fieldErrorCode : SensitivityTuple → ParameterErrorTuple → Nat
fieldErrorCode sensitivity error =
  centreSensitivity sensitivity * centreError error
  + scaleSensitivity sensitivity * scaleError error
  + weightSensitivity sensitivity * weightError error
  + sharpnessSensitivity sensitivity * sharpnessError error

canonicalSensitivity : SensitivityTuple
canonicalSensitivity = sensitivityTuple 2 3 1 4

canonicalFieldErrorCodeIsNine :
  fieldErrorCode
    canonicalSensitivity
    (parameterError exactParameters quantisedParameters)
  ≡
  9
canonicalFieldErrorCodeIsNine = refl

------------------------------------------------------------------------
-- Opposite corners fail as a nonlinear cell enclosure.  The interior point
-- can exceed both sampled corners.

data ParameterCellSample : Set where
  lowerParameterCorner : ParameterCellSample
  upperParameterCorner : ParameterCellSample
  interiorParameterPeak : ParameterCellSample

nonlinearCellResponse : ParameterCellSample → Nat
nonlinearCellResponse lowerParameterCorner = 2
nonlinearCellResponse upperParameterCorner = 4
nonlinearCellResponse interiorParameterPeak = 11

interiorPeakExceedsUpperCorner :
  nonlinearCellResponse interiorParameterPeak
  ≡
  nonlinearCellResponse upperParameterCorner
  →
  ⊥
interiorPeakExceedsUpperCorner ()

record EventSeparationQuantisationBoundary : Set where
  constructor eventSeparationQuantisationBoundary
  field
    emptyNeighbourhoodHasCanonicalMedian : Bool
    emptyNeighbourhoodHasCanonicalMedianIsFalse :
      emptyNeighbourhoodHasCanonicalMedian ≡ false

    externalTimeAutomaticallyCreatesTrajectory : Bool
    externalTimeAutomaticallyCreatesTrajectoryIsFalse :
      externalTimeAutomaticallyCreatesTrajectory ≡ false

    twoParameterCornersEncloseNonlinearCell : Bool
    twoParameterCornersEncloseNonlinearCellIsFalse :
      twoParameterCornersEncloseNonlinearCell ≡ false

    finiteSensitivityCodeIsContinuumLipschitzTheorem : Bool
    finiteSensitivityCodeIsContinuumLipschitzTheoremIsFalse :
      finiteSensitivityCodeIsContinuumLipschitzTheorem ≡ false

open EventSeparationQuantisationBoundary public

canonicalEventSeparationQuantisationBoundary :
  EventSeparationQuantisationBoundary
canonicalEventSeparationQuantisationBoundary =
  eventSeparationQuantisationBoundary false refl false refl false refl false refl
