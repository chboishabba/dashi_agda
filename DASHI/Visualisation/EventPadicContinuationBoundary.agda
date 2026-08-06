module DASHI.Visualisation.EventPadicContinuationBoundary where

open import DASHI.Core.Prelude

import DASHI.Visualisation.EventFilamentFieldExact as Event
import DASHI.Visualisation.SelfConsistentEventRendererExact as Renderer
import DASHI.Biology.TernaryCyclicDialecticExact as Cyclic
import DASHI.Biology.TriadicCarryResidualExact as Carry
import DASHI.Biology.TriadicKernelLiftQuotientExact as Triadic
import DASHI.Biology.RenderablePadicReasoningFieldExact as Padic
import DASHI.Biology.PadicCylinderLODReasoningField as LOD
import DASHI.Visualisation.EventPadicSourceAtlas as Sources

record EventPadicContinuationBoundary : Set where
  field
    eventFieldBoundary : Event.EventFilamentFieldBoundary
    selfConsistentRendererBoundary : Renderer.SelfConsistentRendererBoundary
    ternaryCyclicBoundary : Cyclic.TernaryCyclicDialecticBoundary
    renderablePadicBoundary : Padic.RenderablePadicReasoningBoundary

    additiveEventFieldWitness :
      Event.scalarFieldSample ≡ 10

    correctedSharpnessWitness :
      Event.correctedSharpness Event.crowded ≡ 1
      ×
      Event.correctedSharpness Event.isolated ≡ 3

    temporalGraphForwardWitness :
      Event.Before
        (Event.edgeSource Event.canonicalEdge)
        (Event.edgeTarget Event.canonicalEdge)

    ridgeCodimensionWitness :
      Event.ridgeNormalDirections 4 1 ≡ 3

    finiteFixedPointConvergenceWitness :
      Renderer.iterateTwo Renderer.densitySeed
      ≡
      Renderer.densityFixed

    finiteFixedPointUniquenessWitness :
      (state : Renderer.DensityState) →
      Renderer.fieldOperator state ≡ state →
      state ≡ Renderer.densityFixed

    commonAttenuationCancellationWitness :
      Renderer.baseProfile ≡ Renderer.uniformlyAttenuatedProfile

    cyclicAssociativityWitness :
      (a b c : Carry.TriResidue) →
      Carry.cyclicAdd3 (Carry.cyclicAdd3 a b) c
      ≡
      Carry.cyclicAdd3 a (Carry.cyclicAdd3 b c)

    cyclicInverseWitness :
      (a : Carry.TriResidue) →
      Cyclic.cyclicAdd3 a (Cyclic.inverseResidue a)
      ≡
      Cyclic.zeroResidue

    carryResidualWitness :
      Carry.addCarry3
        Triadic.positiveTrit
        Triadic.positiveTrit
        Triadic.zeroTrit
      ≡
      (Triadic.negativeTrit , Triadic.positiveTrit)

    softOneHotExactnessWitness :
      (a b : Carry.TriResidue) →
      Carry.cyclicConvolution (Carry.basisMass a) (Carry.basisMass b)
      ≡
      Carry.basisMass (Carry.cyclicAdd3 a b)

    characterHomomorphismWitness :
      (a b : Carry.TriResidue) →
      Cyclic.character (Carry.cyclicAdd3 a b)
      ≡
      Cyclic.multiplyRoot (Cyclic.character a) (Cyclic.character b)

    depthNineCountWitness :
      Padic.depthNinePrefixCount ≡ 19683

    depthNineEmbeddingWitness :
      Padic.embedDepthNine Padic.sampleDepthNine
      ≡
      LOD.voxel3 15 23 1

    parentMassWitness :
      LOD.aggregateNat LOD.canonicalChildMasses ≡ 9

    prefixLocalConstancyWitness :
      Padic.prefixKernel Padic.localCylinderPointA
      ≡
      Padic.prefixKernel Padic.localCylinderPointB

    addressRetentionWitness :
      Padic.addressMetadataRetained Padic.canonicalRenderableReasoningField
      ≡
      true

    eventPadicSourceCount :
      Sources.canonicalEventPadicSourceCount ≡ 10

open EventPadicContinuationBoundary public

canonicalEventPadicContinuationBoundary :
  EventPadicContinuationBoundary
canonicalEventPadicContinuationBoundary =
  record
    { eventFieldBoundary = Event.canonicalEventFilamentFieldBoundary
    ; selfConsistentRendererBoundary =
        Renderer.canonicalSelfConsistentRendererBoundary
    ; ternaryCyclicBoundary = Cyclic.canonicalTernaryCyclicDialecticBoundary
    ; renderablePadicBoundary = Padic.canonicalRenderablePadicReasoningBoundary
    ; additiveEventFieldWitness = Event.scalarFieldSampleIsTen
    ; correctedSharpnessWitness = refl , refl
    ; temporalGraphForwardWitness = Event.edgeIsForwardByConstruction
    ; ridgeCodimensionWitness = Event.oneDimensionalRidgeInFourHasThreeNormals
    ; finiteFixedPointConvergenceWitness = Renderer.seedConvergesInTwoSteps
    ; finiteFixedPointUniquenessWitness = Renderer.fixedPointUnique
    ; commonAttenuationCancellationWitness =
        Renderer.uniformAttenuationCancelsFromComposition
    ; cyclicAssociativityWitness = Carry.cyclicAdd3Associative
    ; cyclicInverseWitness = Cyclic.cyclicInverseRight
    ; carryResidualWitness = Carry.positiveOverflowLifts
    ; softOneHotExactnessWitness = Carry.basisConvolutionExact
    ; characterHomomorphismWitness = Cyclic.characterIsHomomorphism
    ; depthNineCountWitness = Padic.depthNineCountIs19683
    ; depthNineEmbeddingWitness = Padic.sampleDepthNineVoxel
    ; parentMassWitness = LOD.canonicalParentMassIsNine
    ; prefixLocalConstancyWitness =
        Padic.kernelLocallyConstantOnDepthTwoCylinder
    ; addressRetentionWitness = Padic.canonicalFieldRetainsAddress
    ; eventPadicSourceCount = Sources.canonicalEventPadicSourceCountIsTen
    }
