module DASHI.Biology.PadicLODConsistencyExact where

open import DASHI.Core.Prelude

import DASHI.Biology.PadicCylinderLODReasoningField as LOD
import DASHI.Biology.RenderablePadicReasoningFieldExact as Renderable
import DASHI.Visualisation.RendererStabilityExact as Stability

------------------------------------------------------------------------
-- Finite exact completion of sections 818--834: mass/class aggregation,
-- adaptive ternary refinement, exact compositing, conditional-expectation zoom,
-- and explicit Euclidean observation loss.

record ChildClassMass : Set where
  constructor childClassMass
  field
    childClassA : Nat
    childClassB : Nat
    childTotalMass : Nat
    childClassesClose :
      childClassA + childClassB ≡ childTotalMass

open ChildClassMass public

lightPureAChild : ChildClassMass
lightPureAChild = childClassMass 1 0 1 refl

heavyPureBChild : ChildClassMass
heavyPureBChild = childClassMass 0 9 9 refl

aggregateClassA : ChildClassMass → ChildClassMass → Nat
aggregateClassA left right = childClassA left + childClassA right

aggregateClassB : ChildClassMass → ChildClassMass → Nat
aggregateClassB left right = childClassB left + childClassB right

aggregateTotalMass : ChildClassMass → ChildClassMass → Nat
aggregateTotalMass left right = childTotalMass left + childTotalMass right

unequalMassAggregateA :
  aggregateClassA lightPureAChild heavyPureBChild ≡ 1
unequalMassAggregateA = refl

unequalMassAggregateB :
  aggregateClassB lightPureAChild heavyPureBChild ≡ 9
unequalMassAggregateB = refl

unequalMassAggregateTotal :
  aggregateTotalMass lightPureAChild heavyPureBChild ≡ 10
unequalMassAggregateTotal = refl

record RationalClassWeight : Set where
  constructor rationalClassWeight
  field
    classNumerator : Nat
    totalDenominator : Nat

open RationalClassWeight public

averageAlreadyNormalisedChildAWeights : RationalClassWeight
averageAlreadyNormalisedChildAWeights = rationalClassWeight 1 2

normaliseAggregatedClassAMass : RationalClassWeight
normaliseAggregatedClassAMass = rationalClassWeight 1 10

crossProductNaiveWeight :
  classNumerator averageAlreadyNormalisedChildAWeights
  * totalDenominator normaliseAggregatedClassAMass
  ≡
  10
crossProductNaiveWeight = refl

crossProductAggregateWeight :
  classNumerator normaliseAggregatedClassAMass
  * totalDenominator averageAlreadyNormalisedChildAWeights
  ≡
  2
crossProductAggregateWeight = refl

unequalMassNormalisationsDiffer :
  averageAlreadyNormalisedChildAWeights
  ≡
  normaliseAggregatedClassAMass
  →
  ⊥
unequalMassNormalisationsDiffer ()

------------------------------------------------------------------------
-- Three-child parent consistency and a finite conditional-expectation tower.

record ThreeChildDensity : Set where
  constructor threeChildDensity
  field
    densityChild0 : Nat
    densityChild1 : Nat
    densityChild2 : Nat
    parentDensity : Nat
    conditionalAverageCloses :
      3 * parentDensity
      ≡ densityChild0 + densityChild1 + densityChild2

open ThreeChildDensity public

canonicalConditionalDensity : ThreeChildDensity
canonicalConditionalDensity = threeChildDensity 1 3 5 3 refl

canonicalParentIsThree :
  parentDensity canonicalConditionalDensity ≡ 3
canonicalParentIsThree = refl

data ZoomDepth : Set where
  coarseDepth : ZoomDepth
  refinedDepth : ZoomDepth

densityAtZoom : ZoomDepth → Nat
densityAtZoom coarseDepth = parentDensity canonicalConditionalDensity
densityAtZoom refinedDepth =
  densityChild0 canonicalConditionalDensity
  + densityChild1 canonicalConditionalDensity
  + densityChild2 canonicalConditionalDensity

coarseExpectationRecoversParent :
  3 * densityAtZoom coarseDepth ≡ densityAtZoom refinedDepth
coarseExpectationRecoversParent = refl

------------------------------------------------------------------------
-- Adaptive refinement and sparse branching.  A product address with r
-- independent ternary coordinates has 3^r children at one refinement step.

pow3 : Nat → Nat
pow3 zero = 1
pow3 (suc n) = 3 * pow3 n

oneCoordinateChildCount : pow3 1 ≡ 3
oneCoordinateChildCount = refl

twoCoordinateChildCount : pow3 2 ≡ 9
twoCoordinateChildCount = refl

threeCoordinateChildCount : pow3 3 ≡ 27
threeCoordinateChildCount = refl

data NodeRetentionReason : Set where
  massAboveThreshold : NodeRetentionReason
  variationAboveThreshold : NodeRetentionReason
  prunedNode : NodeRetentionReason

retentionDecision : Nat → Nat → NodeRetentionReason
retentionDecision zero zero = prunedNode
retentionDecision zero (suc variation) = variationAboveThreshold
retentionDecision (suc mass) variation = massAboveThreshold

zeroMassHighVariationRetained :
  retentionDecision 0 4 ≡ variationAboveThreshold
zeroMassHighVariationRetained = refl

zeroMassZeroVariationPruned :
  retentionDecision 0 0 ≡ prunedNode
zeroMassZeroVariationPruned = refl

------------------------------------------------------------------------
-- Prefix cells and exact rendering modes.

data PrefixCellDepth : Set where
  sourceDepthThree : PrefixCellDepth
  sourceDepthSix : PrefixCellDepth
  sourceDepthNine : PrefixCellDepth

cellSideDenominator : PrefixCellDepth → Nat
cellSideDenominator sourceDepthThree = 3
cellSideDenominator sourceDepthSix = 9
cellSideDenominator sourceDepthNine = 27

sourceDepthNineSideIsTwentySeven :
  cellSideDenominator sourceDepthNine ≡ 27
sourceDepthNineSideIsTwentySeven = refl

data RenderSemantics : Set where
  strongestSampleSemantics : RenderSemantics
  accumulatedOpacitySemantics : RenderSemantics
  integratedEmissionSemantics : RenderSemantics
  boundarySurfaceSemantics : RenderSemantics

canonicalStraightAlphaColour :
  Stability.frontToBackColour
    Stability.half
    Stability.half
    Stability.one
    Stability.threeQuarters
  ≡
  Stability.fraction 14 16
canonicalStraightAlphaColour = Stability.canonicalCompositedColour

canonicalStraightAlphaOpacity :
  Stability.frontToBackAlpha Stability.half Stability.threeQuarters
  ≡
  Stability.fraction 14 16
canonicalStraightAlphaOpacity = Stability.canonicalCompositedAlpha

------------------------------------------------------------------------
-- Direct ray evaluation must retain a boundary convention and should prefer
-- the original symbolic address over recovering it from floating point.

data BoundaryConvention : Set where
  halfOpenVoxelCells : BoundaryConvention
  canonicalNonEventuallyTwoExpansion : BoundaryConvention
  retainedSymbolicAddress : BoundaryConvention

recommendedBoundaryConvention : BoundaryConvention
recommendedBoundaryConvention = retainedSymbolicAddress

------------------------------------------------------------------------
-- Finite cache law is inherited from the local-constancy theorem.

cacheLaw :
  Renderable.prefixKernel Renderable.localCylinderPointA
  ≡
  Renderable.prefixKernel Renderable.localCylinderPointB
cacheLaw = Renderable.kernelLocallyConstantOnDepthTwoCylinder

parentMassLaw :
  LOD.aggregateNat LOD.canonicalChildMasses ≡ 9
parentMassLaw = LOD.canonicalParentMassIsNine

------------------------------------------------------------------------
-- Every loss-bearing Euclidean observation stage is explicit.

data PadicObservationStage : Set where
  exactPrefixTreeStage : PadicObservationStage
  euclideanCellStage : PadicObservationStage
  interpolatedVolumeStage : PadicObservationStage
  compositedRayStage : PadicObservationStage
  projectedImageStage : PadicObservationStage

nextObservationStage : PadicObservationStage → PadicObservationStage
nextObservationStage exactPrefixTreeStage = euclideanCellStage
nextObservationStage euclideanCellStage = interpolatedVolumeStage
nextObservationStage interpolatedVolumeStage = compositedRayStage
nextObservationStage compositedRayStage = projectedImageStage
nextObservationStage projectedImageStage = projectedImageStage

observationReachesImageInFourSteps :
  nextObservationStage
    (nextObservationStage
      (nextObservationStage
        (nextObservationStage exactPrefixTreeStage)))
  ≡
  projectedImageStage
observationReachesImageInFourSteps = refl

data RecoveryStatus : Set where
  exactAddressRecovery : RecoveryStatus
  recoveryWithStoredMetadata : RecoveryStatus
  noninjectiveImageRecovery : RecoveryStatus

recoveryAfterStage : PadicObservationStage → RecoveryStatus
recoveryAfterStage exactPrefixTreeStage = exactAddressRecovery
recoveryAfterStage euclideanCellStage = recoveryWithStoredMetadata
recoveryAfterStage interpolatedVolumeStage = recoveryWithStoredMetadata
recoveryAfterStage compositedRayStage = noninjectiveImageRecovery
recoveryAfterStage projectedImageStage = noninjectiveImageRecovery

finalImageRecoveryIsNoninjective :
  recoveryAfterStage projectedImageStage ≡ noninjectiveImageRecovery
finalImageRecoveryIsNoninjective = refl

record PadicLODConsistencyBoundary : Set where
  constructor padicLODConsistencyBoundary
  field
    averagingChildWeightsEqualsMassWeightedParent : Bool
    averagingChildWeightsEqualsMassWeightedParentIsFalse :
      averagingChildWeightsEqualsMassWeightedParent ≡ false

    fullEuclideanCubeIsPrimaryReasoningState : Bool
    fullEuclideanCubeIsPrimaryReasoningStateIsFalse :
      fullEuclideanCubeIsPrimaryReasoningState ≡ false

    maximumIntensityAndAlphaCompositingHaveSameSemantics : Bool
    maximumIntensityAndAlphaCompositingHaveSameSemanticsIsFalse :
      maximumIntensityAndAlphaCompositingHaveSameSemantics ≡ false

    conditionalAverageMeansFineDigitsAreRecoverable : Bool
    conditionalAverageMeansFineDigitsAreRecoverableIsFalse :
      conditionalAverageMeansFineDigitsAreRecoverable ≡ false

open PadicLODConsistencyBoundary public

canonicalPadicLODConsistencyBoundary : PadicLODConsistencyBoundary
canonicalPadicLODConsistencyBoundary =
  padicLODConsistencyBoundary false refl false refl false refl false refl
