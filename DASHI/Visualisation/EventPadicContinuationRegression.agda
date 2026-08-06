module DASHI.Visualisation.EventPadicContinuationRegression where

open import DASHI.Core.Prelude

import DASHI.Visualisation.EventFilamentFieldExact as Event
import DASHI.Visualisation.SelfConsistentEventRendererExact as Renderer
import DASHI.Biology.TernaryCyclicDialecticExact as Cyclic
import DASHI.Biology.TriadicCarryResidualExact as Carry
import DASHI.Biology.TriadicKernelLiftQuotientExact as Triadic
import DASHI.Biology.RenderablePadicReasoningFieldExact as Padic
import DASHI.Biology.PadicCylinderLODReasoningField as LOD
import DASHI.Visualisation.EventPadicSourceAtlas as Sources
import DASHI.Visualisation.EventPadicContinuationBoundary as Boundary

continuationBoundaryExists : Boundary.EventPadicContinuationBoundary
continuationBoundaryExists = Boundary.canonicalEventPadicContinuationBoundary

eventFieldRegression : Event.scalarFieldSample ≡ 10
eventFieldRegression = refl

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
  Carry.mass3 1 1 2
softConvolutionRegression = refl

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

sourceCountRegression :
  Sources.canonicalEventPadicSourceCount ≡ 10
sourceCountRegression = Sources.canonicalEventPadicSourceCountIsTen
