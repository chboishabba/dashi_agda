module DASHI.Visualisation.EventPadicContinuationRegression where

open import DASHI.Core.Prelude

import DASHI.Visualisation.EventFilamentFieldExact as Event
import DASHI.Visualisation.EventLabelGeometryExact as Labels
import DASHI.Visualisation.FiniteAnisotropicKernelExact as Anisotropic
import DASHI.Visualisation.EventFilamentPersistenceExact as Persistence
import DASHI.Visualisation.SelfConsistentEventRendererExact as Renderer
import DASHI.Visualisation.RendererStabilityExact as Stability
import DASHI.Biology.TernaryCyclicDialecticExact as Cyclic
import DASHI.Biology.TernarySoftCarryLogicExact as Soft
import DASHI.Biology.TriadicCarryResidualExact as Carry
import DASHI.Biology.TriadicKernelLiftQuotientExact as Triadic
import DASHI.Biology.RenderablePadicReasoningFieldExact as Padic
import DASHI.Biology.PadicLODConsistencyExact as Consistency
import DASHI.Biology.PadicCylinderLODReasoningField as LOD
import DASHI.Visualisation.EventPadicSourceAtlas as Sources
import DASHI.Visualisation.EventPadicContinuationBoundary as Boundary

continuationBoundaryExists : Boundary.EventPadicContinuationBoundary
continuationBoundaryExists = Boundary.canonicalEventPadicContinuationBoundary

eventFieldRegression : Event.scalarFieldSample ≡ 10
eventFieldRegression = refl

labelProductDistanceRegression :
  Labels.productLabelDistance Labels.labelA Labels.labelB ≡ 2
labelProductDistanceRegression = Labels.labelABDistanceIsTwo

labelFactorIndependenceRegression :
  Labels.binaryHammingDistance
    (Event.binaryLabel Labels.labelA)
    (Event.binaryLabel Labels.sameBinaryDifferentHierarchy)
  ≡
  0
  ×
  Labels.prefixDistanceCode
    (Event.hierarchyLabel Labels.labelA)
    (Event.hierarchyLabel Labels.sameBinaryDifferentHierarchy)
  ≡
  3
labelFactorIndependenceRegression =
  Labels.binaryDistanceCanVanishWhileHierarchyDiffers

anisotropicRadiusRegression :
  Anisotropic.mahalanobisNumerator
    Anisotropic.canonicalEllipticEvent
    Anisotropic.canonicalQuery
  ≡
  2 *
  Anisotropic.mahalanobisDenominator
    Anisotropic.canonicalEllipticEvent
anisotropicRadiusRegression = Anisotropic.canonicalSquaredRadiusIsTwo

anisotropicClassFieldRegression :
  Anisotropic.finiteClassField
  ≡
  Anisotropic.classContribution3 15 17 2
anisotropicClassFieldRegression = refl

normalisedKernelRowRegression :
  Anisotropic.scaledKernelRowMass 5 Anisotropic.canonicalKernelRow
  ≡
  5 * Anisotropic.kernelDenominator Anisotropic.canonicalKernelRow
normalisedKernelRowRegression = refl

positiveKernelRegression :
  Event.positiveWrapper Event.negativeRawResponse ≡ 0
positiveKernelRegression = refl

timeDoesNotCreateWormRegression :
  Event.timeLabelAloneAppearance Event.ambientTimeCoordinate
  ≡
  Event.explicitWorm
  →
  ⊥
timeDoesNotCreateWormRegression = Event.timeCoordinateDoesNotForceWorm

thresholdPersistenceRegression :
  Persistence.SuperlevelMember Persistence.highThreshold Persistence.event0
  →
  Persistence.SuperlevelMember Persistence.lowThreshold Persistence.event0
thresholdPersistenceRegression = Persistence.highIncludedInLow

stochasticRowRegression :
  Persistence.toEventOneMass Persistence.canonicalTransitionRow
  + Persistence.toEventTwoMass Persistence.canonicalTransitionRow
  ≡
  Persistence.rowDenominator Persistence.canonicalTransitionRow
stochasticRowRegression = Persistence.canonicalTransitionRowCloses

ridgeCodimensionRegression :
  Event.ridgeNormalDirections 4 1 ≡ 3
ridgeCodimensionRegression = refl

fixedPointRegression :
  Renderer.fieldOperator Renderer.densityFixed
  ≡
  Renderer.densityFixed
fixedPointRegression = refl

fixedPointUniquenessRegression :
  (state : Renderer.DensityState) →
  Renderer.fieldOperator state ≡ state →
  state ≡ Renderer.densityFixed
fixedPointUniquenessRegression = Renderer.fixedPointUnique

straightAlphaRegression :
  Stability.frontToBackAlpha Stability.half Stability.threeQuarters
  ≡
  Stability.fraction 14 16
straightAlphaRegression = Stability.canonicalCompositedAlpha

frameCalibrationRegression :
  Stability.calibratedFraction Stability.smallFrame
  ≡
  Stability.calibratedFraction Stability.largeFrameWithDistantPeak
  →
  ⊥
frameCalibrationRegression = Stability.calibrationFractionsDiffer

cmykNonlinearityRegression :
  Renderer.convertedTogether
  ≡
  Renderer.convertedSeparatelyThenAdded
  →
  ⊥
cmykNonlinearityRegression = Renderer.cmykConversionIsNotAdditive

cyclicIdentityRegression :
  (a : Carry.TriResidue) →
  Cyclic.cyclicAdd3 a Cyclic.zeroResidue ≡ a
cyclicIdentityRegression = Cyclic.cyclicIdentityRight

cyclicNonSelfCancellationRegression :
  Cyclic.cyclicAdd3 Carry.residue1 Carry.residue1
  ≡
  Carry.residue0
  →
  ⊥
cyclicNonSelfCancellationRegression = Cyclic.nonzeroSelfCancellationFails

texNoncommutativeRegression :
  Cyclic.tex Triadic.negativeTrit Triadic.zeroTrit
  ≡
  Cyclic.tex Triadic.zeroTrit Triadic.negativeTrit
  →
  ⊥
texNoncommutativeRegression = Cyclic.texIsNotCommutative

softConvolutionRegression :
  Carry.cyclicConvolution Cyclic.softInputP Cyclic.softInputQ
  ≡
  Carry.mass3 2 1 1
softConvolutionRegression = Cyclic.softConvolutionSample

softCarryRegression :
  Soft.carryPairMassTotal
    (Soft.hardCarryAsSoftOneHot
      Triadic.positiveTrit
      Triadic.positiveTrit
      Triadic.zeroTrit)
  ≡
  1
softCarryRegression = refl

designationSchemeRegression :
  Soft.onePremiseConsequence
    Soft.trueOnlyScheme
    Soft.schemeSensitiveValuation
    Soft.propositionP
    Soft.propositionQ
  ≡
  true
  ×
  Soft.onePremiseConsequence
    Soft.neutralOrTrueScheme
    Soft.schemeSensitiveValuation
    Soft.propositionP
    Soft.propositionQ
  ≡
  false
designationSchemeRegression = refl , refl

carryRegression :
  Carry.addCarry3
    Triadic.positiveTrit
    Triadic.positiveTrit
    Triadic.zeroTrit
  ≡
  (Triadic.negativeTrit , Triadic.positiveTrit)
carryRegression = Carry.positiveOverflowLifts

depthNineCountRegression : Padic.depthNinePrefixCount ≡ 19683
depthNineCountRegression = refl

depthNineEmbeddingRegression :
  Padic.embedDepthNine Padic.sampleDepthNine
  ≡
  LOD.voxel3 15 23 1
depthNineEmbeddingRegression = refl

quotientLossRegression :
  Padic.sameParentChild3 ≡ Padic.sameParentChild9 → ⊥
quotientLossRegression = Padic.childrenRemainDistinct

opacityContrastFailureRegression :
  Padic.badPerVoxelOpacity Padic.lowPositiveDensity
  ≡
  Padic.badPerVoxelOpacity Padic.highPositiveDensity
opacityContrastFailureRegression = refl

parentMassRegression :
  LOD.aggregateNat LOD.canonicalChildMasses ≡ 9
parentMassRegression = refl

conditionalZoomRegression :
  3 * Consistency.densityAtZoom Consistency.coarseDepth
  ≡
  Consistency.densityAtZoom Consistency.refinedDepth
conditionalZoomRegression = refl

massWeightedNormalisationRegression :
  Consistency.averageAlreadyNormalisedChildAWeights
  ≡
  Consistency.normaliseAggregatedClassAMass
  →
  ⊥
massWeightedNormalisationRegression =
  Consistency.unequalMassNormalisationsDiffer

sourceCountRegression :
  Sources.canonicalEventPadicSourceCount ≡ 10
sourceCountRegression = Sources.canonicalEventPadicSourceCountIsTen
