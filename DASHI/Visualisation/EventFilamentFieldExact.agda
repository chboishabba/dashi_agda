module DASHI.Visualisation.EventFilamentFieldExact where

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- Finite exact event -> filament-field spine for supplied sections 671--709.
-- Continuous covariance matrices, integrals, ridge regularity, and statistical
-- consistency remain explicit external obligations.  The finite model proves
-- the algebraic distinctions required before those analytic layers are added.

data BinaryBit : Set where
  bit0 : BinaryBit
  bit1 : BinaryBit

data TernaryDigit : Set where
  digit0 : TernaryDigit
  digit1 : TernaryDigit
  digit2 : TernaryDigit

record BinaryCorner : Set where
  constructor binaryCorner
  field
    cornerFirst : BinaryBit
    cornerSecond : BinaryBit

open BinaryCorner public

record TernaryAddress2 : Set where
  constructor ternaryAddress2
  field
    addressFirst : TernaryDigit
    addressSecond : TernaryDigit

open TernaryAddress2 public

record ProductLabel : Set where
  constructor productLabel
  field
    binaryLabel : BinaryCorner
    hierarchyLabel : TernaryAddress2

open ProductLabel public

canonicalProductLabel : ProductLabel
canonicalProductLabel =
  productLabel
    (binaryCorner bit1 bit0)
    (ternaryAddress2 digit2 digit1)

binaryLabelRecoverable :
  binaryLabel canonicalProductLabel ≡ binaryCorner bit1 bit0
binaryLabelRecoverable = refl

hierarchyLabelRecoverable :
  hierarchyLabel canonicalProductLabel ≡ ternaryAddress2 digit2 digit1
hierarchyLabelRecoverable = refl

binaryCornerCount : Nat
binaryCornerCount = 4

ternaryAddressTwoDigitCount : Nat
ternaryAddressTwoDigitCount = 9

productLabelCount : Nat
productLabelCount = binaryCornerCount * ternaryAddressTwoDigitCount

productLabelCountIsThirtySix : productLabelCount ≡ 36
productLabelCountIsThirtySix = refl

data LabelMetric : Set where
  hammingCornerMetric : LabelMetric
  prefixHierarchyMetric : LabelMetric
  productLabelMetric : LabelMetric

------------------------------------------------------------------------
-- Event record.  Full SPD matrices are represented by a declared covariance
-- mode plus exact axis scales in this finite executable shadow.

data CovarianceMode : Set where
  diagonalCovariance : CovarianceMode
  fullPositiveDefiniteCovariance : CovarianceMode

record ClassMass3 : Set where
  constructor classMass3
  field
    classA : Nat
    classB : Nat
    classC : Nat

open ClassMass3 public

classTotal : ClassMass3 → Nat
classTotal masses = classA masses + classB masses + classC masses

record Event : Set where
  constructor event
  field
    centreX : Nat
    centreY : Nat
    scaleParallel : Nat
    scaleNormal : Nat
    salience : Nat
    timestamp : Nat
    eventLabel : ProductLabel
    classContribution : ClassMass3
    covarianceMode : CovarianceMode

open Event public

canonicalEvent : Event
canonicalEvent =
  event
    2 3
    4 1
    5 7
    canonicalProductLabel
    (classMass3 2 1 0)
    fullPositiveDefiniteCovariance

canonicalEventHasAnisotropy :
  scaleParallel canonicalEvent ≡ 4
  ×
  scaleNormal canonicalEvent ≡ 1
canonicalEventHasAnisotropy = refl , refl

------------------------------------------------------------------------
-- Separation and sharpness.  The corrected map is monotone increasing in the
-- declared finite separation order; the legacy inverse map has the opposite
-- direction.

data Separation : Set where
  crowded : Separation
  intermediate : Separation
  isolated : Separation

separationCode : Separation → Nat
separationCode crowded = 0
separationCode intermediate = 1
separationCode isolated = 2

correctedSharpness : Separation → Nat
correctedSharpness crowded = 1
correctedSharpness intermediate = 2
correctedSharpness isolated = 3

legacyInverseSharpness : Separation → Nat
legacyInverseSharpness crowded = 3
legacyInverseSharpness intermediate = 2
legacyInverseSharpness isolated = 1

correctedSharpnessIsIncreasing :
  correctedSharpness crowded ≡ 1
  ×
  correctedSharpness intermediate ≡ 2
  ×
  correctedSharpness isolated ≡ 3
correctedSharpnessIsIncreasing = refl , (refl , refl)

legacyRuleReversesIntendedDirection :
  legacyInverseSharpness crowded ≡ 3
  ×
  legacyInverseSharpness isolated ≡ 1
legacyRuleReversesIntendedDirection = refl , refl

record KernelShape : Set where
  constructor kernelShape
  field
    geometricExtent : Nat
    boundarySteepness : Nat

open KernelShape public

sameRenderedWidthCandidateOne : KernelShape
sameRenderedWidthCandidateOne = kernelShape 2 4

sameRenderedWidthCandidateTwo : KernelShape
sameRenderedWidthCandidateTwo = kernelShape 4 2

shapeParametersRemainDistinct :
  sameRenderedWidthCandidateOne ≡ sameRenderedWidthCandidateTwo → ⊥
shapeParametersRemainDistinct ()

------------------------------------------------------------------------
-- Signed GELU output is not density.  A positive wrapper creates a separate
-- carrier before event contributions are added.

data RawKernelSign : Set where
  negativeRawResponse : RawKernelSign
  zeroRawResponse : RawKernelSign
  positiveRawResponse : RawKernelSign

positiveWrapper : RawKernelSign → Nat
positiveWrapper negativeRawResponse = 0
positiveWrapper zeroRawResponse = 0
positiveWrapper positiveRawResponse = 2

negativeRawKernelContributesNoPositiveMass :
  positiveWrapper negativeRawResponse ≡ 0
negativeRawKernelContributesNoPositiveMass = refl

record EventKernelSample : Set where
  constructor eventKernelSample
  field
    sourceWeight : Nat
    positiveKernelValue : Nat

open EventKernelSample public

kernelContribution : EventKernelSample → Nat
kernelContribution sample =
  sourceWeight sample * positiveKernelValue sample

sampleOne : EventKernelSample
sampleOne = eventKernelSample 3 2

sampleTwo : EventKernelSample
sampleTwo = eventKernelSample 4 1

scalarFieldSample : Nat
scalarFieldSample = kernelContribution sampleOne + kernelContribution sampleTwo

scalarFieldSampleIsTen : scalarFieldSample ≡ 10
scalarFieldSampleIsTen = refl

normalisedKernelMass : EventKernelSample → Nat
normalisedKernelMass sample = sourceWeight sample

normalisedKernelMassAdds :
  normalisedKernelMass sampleOne + normalisedKernelMass sampleTwo ≡ 7
normalisedKernelMassAdds = refl

classFieldSample : ClassMass3
classFieldSample = classMass3 4 3 3

classFieldCloses : classTotal classFieldSample ≡ 10
classFieldCloses = refl

record MixtureCertificate : Set where
  constructor mixtureCertificate
  field
    mixtureNumerators : ClassMass3
    mixtureDenominator : Nat
    numeratorsClose :
      classTotal mixtureNumerators ≡ mixtureDenominator

open MixtureCertificate public

canonicalMixtureCertificate : MixtureCertificate
canonicalMixtureCertificate =
  mixtureCertificate classFieldSample 10 refl

------------------------------------------------------------------------
-- Time may be carried as a coordinate or as an external parameter.  Neither
-- choice creates a trajectory without overlap or an explicit path carrier.

data TimeOrganisation : Set where
  ambientTimeCoordinate : TimeOrganisation
  externalTimeParameter : TimeOrganisation

data EventAppearance : Set where
  isolatedBeads : EventAppearance
  overlappingBeads : EventAppearance
  explicitWorm : EventAppearance

timeLabelAloneAppearance : TimeOrganisation → EventAppearance
timeLabelAloneAppearance ambientTimeCoordinate = isolatedBeads
timeLabelAloneAppearance externalTimeParameter = isolatedBeads

timeCoordinateDoesNotForceWorm :
  timeLabelAloneAppearance ambientTimeCoordinate ≡ explicitWorm → ⊥
timeCoordinateDoesNotForceWorm ()

record TrajectorySegment : Set where
  constructor trajectorySegment
  field
    startEvent : Nat
    middleEvent : Nat
    endEvent : Nat
    lineDensity : Nat
    parallelScale : Nat
    normalScale : Nat

open TrajectorySegment public

canonicalTrajectory : TrajectorySegment
canonicalTrajectory = trajectorySegment 1 2 3 4 5 1

canonicalTubeIsTangentElongated :
  parallelScale canonicalTrajectory ≡ 5
  ×
  normalScale canonicalTrajectory ≡ 1
canonicalTubeIsTangentElongated = refl , refl

------------------------------------------------------------------------
-- Temporal graph and second-order turn cost.

data TimePoint3 : Set where
  time0 : TimePoint3
  time1 : TimePoint3
  time2 : TimePoint3

data Before : TimePoint3 → TimePoint3 → Set where
  time0Before1 : Before time0 time1
  time1Before2 : Before time1 time2
  time0Before2 : Before time0 time2

record TemporalEdge : Set where
  constructor temporalEdge
  field
    edgeSource : TimePoint3
    edgeTarget : TimePoint3
    forwardWitness : Before edgeSource edgeTarget
    similarityScore : Nat
    distancePenalty : Nat

open TemporalEdge public

canonicalEdge : TemporalEdge
canonicalEdge = temporalEdge time0 time1 time0Before1 5 1

edgeIsForwardByConstruction :
  Before (edgeSource canonicalEdge) (edgeTarget canonicalEdge)
edgeIsForwardByConstruction = forwardWitness canonicalEdge

record TurnTriple : Set where
  constructor turnTriple
  field
    turnStart : TimePoint3
    turnMiddle : TimePoint3
    turnEnd : TimePoint3
    turnPenalty : Nat

open TurnTriple public

canonicalTurn : TurnTriple
canonicalTurn = turnTriple time0 time1 time2 2

turnCostNeedsThreeEvents : turnPenalty canonicalTurn ≡ 2
turnCostNeedsThreeEvents = refl

------------------------------------------------------------------------
-- Hard path, branching, and probabilistic assignments are distinct types.

data ThreadAssignmentMode : Set where
  hardPathAssignment : ThreadAssignmentMode
  branchingAssignment : ThreadAssignmentMode
  probabilisticAssignment : ThreadAssignmentMode

record InferredSegment : Set where
  constructor inferredSegment
  field
    provenanceStart : Nat
    provenanceEnd : Nat
    provenanceScore : Nat
    assignmentMode : ThreadAssignmentMode

open InferredSegment public

canonicalInferredSegment : InferredSegment
canonicalInferredSegment =
  inferredSegment 17 23 9 hardPathAssignment

stitchingProvenanceRetained :
  provenanceStart canonicalInferredSegment ≡ 17
  ×
  provenanceEnd canonicalInferredSegment ≡ 23
  ×
  provenanceScore canonicalInferredSegment ≡ 9
stitchingProvenanceRetained = refl , (refl , refl)

------------------------------------------------------------------------
-- Inverse-density rendering changes observation polarity only.

inverseIntensity : Nat → Nat → Nat
inverseIntensity calibration density = calibration ∸ density

higherDensityIsDarkerWitness :
  inverseIntensity 10 8 ≡ 2
  ×
  inverseIntensity 10 3 ≡ 7
higherDensityIsDarkerWitness = refl , refl

data RegionObservation : Set where
  levelSurface : RegionObservation
  superlevelRegion : RegionObservation
  voidSublevelRegion : RegionObservation

record ThresholdFamily : Set where
  constructor thresholdFamily
  field
    highThreshold : Nat
    lowThreshold : Nat
    highRegionMass : Nat
    lowRegionMass : Nat

open ThresholdFamily public

canonicalThresholdFamily : ThresholdFamily
canonicalThresholdFamily = thresholdFamily 8 4 3 7

lowerThresholdIncludesMoreMass :
  highRegionMass canonicalThresholdFamily ≡ 3
  ×
  lowRegionMass canonicalThresholdFamily ≡ 7
lowerThresholdIncludesMoreMass = refl , refl

------------------------------------------------------------------------
-- Ridge codimension and slice authority.

ridgeNormalDirections : Nat → Nat → Nat
ridgeNormalDirections ambientDimension ridgeDimension =
  ambientDimension ∸ ridgeDimension

oneDimensionalRidgeInFourHasThreeNormals :
  ridgeNormalDirections 4 1 ≡ 3
oneDimensionalRidgeInFourHasThreeNormals = refl

record RidgeSignature : Set where
  constructor ridgeSignature
  field
    ambientDimension : Nat
    ridgeDimension : Nat
    transverseGradientZeros : Nat
    negativeTransverseEigenvalues : Nat

open RidgeSignature public

canonicalOneRidgeSignature : RidgeSignature
canonicalOneRidgeSignature = ridgeSignature 4 1 3 3

canonicalRidgeHasThreeNegativeTransverseModes :
  negativeTransverseEigenvalues canonicalOneRidgeSignature ≡ 3
canonicalRidgeHasThreeNegativeTransverseModes = refl

data RidgeTestScope : Set where
  ambientRidgeTest : RidgeTestScope
  sliceRestrictedRidgeTest : RidgeTestScope

record RidgeCoherence : Set where
  constructor ridgeCoherence
  field
    tangentAlignment : Nat
    normalContraction : Nat
    integratedDensity : Nat

open RidgeCoherence public

canonicalRidgeCoherence : RidgeCoherence
canonicalRidgeCoherence = ridgeCoherence 3 4 12

threadPersistenceScore : RidgeCoherence → Nat
threadPersistenceScore coherence =
  tangentAlignment coherence
  + normalContraction coherence
  + integratedDensity coherence

canonicalThreadPersistenceIsNineteen :
  threadPersistenceScore canonicalRidgeCoherence ≡ 19
canonicalThreadPersistenceIsNineteen = refl

------------------------------------------------------------------------
-- Quantisation error is decomposed into weight and kernel perturbations.  Two
-- sampled corners are explicitly not promoted to an interval enclosure.

record FieldPerturbationBudget : Set where
  constructor fieldPerturbationBudget
  field
    weightError : Nat
    centreError : Nat
    covarianceError : Nat
    sharpnessError : Nat

open FieldPerturbationBudget public

totalPerturbationBound : FieldPerturbationBudget → Nat
totalPerturbationBound budget =
  weightError budget
  + centreError budget
  + covarianceError budget
  + sharpnessError budget

canonicalPerturbationBudget : FieldPerturbationBudget
canonicalPerturbationBudget = fieldPerturbationBudget 1 2 3 1

canonicalPerturbationBoundIsSeven :
  totalPerturbationBound canonicalPerturbationBudget ≡ 7
canonicalPerturbationBoundIsSeven = refl

------------------------------------------------------------------------
-- Parameter effects are distinguished rather than collapsed into one visual
-- knob.  These are qualitative finite labels, not continuum monotonicity
-- theorems for every kernel family.

data ParameterEffect : Set where
  sharperBoundary : ParameterEffect
  narrowerGeometry : ParameterEffect
  largerTotalContribution : ParameterEffect

sharpnessEffect : ParameterEffect
sharpnessEffect = sharperBoundary

covarianceEffect : ParameterEffect
covarianceEffect = narrowerGeometry

salienceEffect : ParameterEffect
salienceEffect = largerTotalContribution

data PlaneBoundingEvidence : Set where
  twoCornerHeuristic : PlaneBoundingEvidence
  intervalEnclosure : PlaneBoundingEvidence
  monotoneEnclosure : PlaneBoundingEvidence
  lipschitzBranchBound : PlaneBoundingEvidence

record EventFilamentFieldBoundary : Set where
  constructor eventFilamentFieldBoundary
  field
    rawGELUIsPositiveDensity : Bool
    rawGELUIsPositiveDensityIsFalse :
      rawGELUIsPositiveDensity ≡ false

    timestampedBeadsAreAutomaticallyTrajectories : Bool
    timestampedBeadsAreAutomaticallyTrajectoriesIsFalse :
      timestampedBeadsAreAutomaticallyTrajectories ≡ false

    binaryCornerIsTernaryHierarchy : Bool
    binaryCornerIsTernaryHierarchyIsFalse :
      binaryCornerIsTernaryHierarchy ≡ false

    oneAdicIsStandardNumberField : Bool
    oneAdicIsStandardNumberFieldIsFalse :
      oneAdicIsStandardNumberField ≡ false

    sliceRidgeIsAutomaticallyAmbientRidge : Bool
    sliceRidgeIsAutomaticallyAmbientRidgeIsFalse :
      sliceRidgeIsAutomaticallyAmbientRidge ≡ false

    twoPlaneSamplesCertifyParameterCell : Bool
    twoPlaneSamplesCertifyParameterCellIsFalse :
      twoPlaneSamplesCertifyParameterCell ≡ false

    inferredWormIsObservedContinuousThought : Bool
    inferredWormIsObservedContinuousThoughtIsFalse :
      inferredWormIsObservedContinuousThought ≡ false

open EventFilamentFieldBoundary public

canonicalEventFilamentFieldBoundary : EventFilamentFieldBoundary
canonicalEventFilamentFieldBoundary =
  eventFilamentFieldBoundary
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
