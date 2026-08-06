module DASHI.Visualisation.EventPadicContinuationBoundary where

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
import DASHI.Biology.PadicRenderModeCorrectionExact as RenderCorrection
import DASHI.Biology.PadicCylinderLODReasoningField as LOD
import DASHI.Visualisation.EventPadicSourceAtlas as Sources

record EventPadicContinuationBoundary : Set where
  field
    eventFieldBoundary : Event.EventFilamentFieldBoundary
    eventLabelGeometryBoundary : Labels.EventLabelGeometryBoundary
    finiteAnisotropicKernelBoundary :
      Anisotropic.FiniteAnisotropicKernelBoundary
    eventPersistenceBoundary : Persistence.EventFilamentPersistenceBoundary
    selfConsistentRendererBoundary : Renderer.SelfConsistentRendererBoundary
    rendererStabilityBoundary : Stability.RendererStabilityBoundary
    ternaryCyclicBoundary : Cyclic.TernaryCyclicDialecticBoundary
    ternarySoftCarryLogicBoundary : Soft.TernarySoftCarryLogicBoundary
    renderablePadicBoundary : Padic.RenderablePadicReasoningBoundary
    padicLODConsistencyBoundary : Consistency.PadicLODConsistencyBoundary
    padicRenderModeCorrectionBoundary :
      RenderCorrection.PadicRenderModeCorrectionBoundary

    additiveEventFieldWitness :
      Event.scalarFieldSample ≡ 10

    labelProductDistanceWitness :
      Labels.productLabelDistance Labels.labelA Labels.labelB ≡ 2

    labelFactorIndependenceWitness :
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

    anisotropicRadiusWitness :
      Anisotropic.mahalanobisNumerator
        Anisotropic.canonicalEllipticEvent
        Anisotropic.canonicalQuery
      ≡
      2 *
      Anisotropic.mahalanobisDenominator
        Anisotropic.canonicalEllipticEvent

    finiteTubeQuadratureWitness :
      Anisotropic.tubeMass Anisotropic.canonicalTubeQuadrature ≡ 10

    correctedSharpnessWitness :
      Event.correctedSharpness Event.crowded ≡ 1
      ×
      Event.correctedSharpness Event.isolated ≡ 3

    temporalGraphForwardWitness :
      Event.Before
        (Event.edgeSource Event.canonicalEdge)
        (Event.edgeTarget Event.canonicalEdge)

    thresholdFiltrationWitness :
      {event : Persistence.EventId} →
      Persistence.SuperlevelMember Persistence.highThreshold event →
      Persistence.SuperlevelMember Persistence.lowThreshold event

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

    exactStraightAlphaWitness :
      Stability.frontToBackAlpha Stability.half Stability.threeQuarters
      ≡
      Stability.fraction 14 16

    legacyStraightAlphaRejected :
      RenderCorrection.legacyStraightAlphaCode
      ≡
      RenderCorrection.exactStraightAlphaNumerator
      →
      ⊥

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

    softCarryMassWitness :
      (x y carry : Triadic.KernelTrit) →
      Soft.carryPairMassTotal (Soft.hardCarryAsSoftOneHot x y carry)
      ≡
      1

    designationChoiceWitness :
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

    conditionalZoomWitness :
      3 * Consistency.densityAtZoom Consistency.coarseDepth
      ≡
      Consistency.densityAtZoom Consistency.refinedDepth

    unequalMassNormalisationWitness :
      Consistency.averageAlreadyNormalisedChildAWeights
      ≡
      Consistency.normaliseAggregatedClassAMass
      →
      ⊥

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
    ; eventLabelGeometryBoundary = Labels.canonicalEventLabelGeometryBoundary
    ; finiteAnisotropicKernelBoundary =
        Anisotropic.canonicalFiniteAnisotropicKernelBoundary
    ; eventPersistenceBoundary =
        Persistence.canonicalEventFilamentPersistenceBoundary
    ; selfConsistentRendererBoundary =
        Renderer.canonicalSelfConsistentRendererBoundary
    ; rendererStabilityBoundary =
        Stability.canonicalRendererStabilityBoundary
    ; ternaryCyclicBoundary = Cyclic.canonicalTernaryCyclicDialecticBoundary
    ; ternarySoftCarryLogicBoundary =
        Soft.canonicalTernarySoftCarryLogicBoundary
    ; renderablePadicBoundary = Padic.canonicalRenderablePadicReasoningBoundary
    ; padicLODConsistencyBoundary =
        Consistency.canonicalPadicLODConsistencyBoundary
    ; padicRenderModeCorrectionBoundary =
        RenderCorrection.canonicalPadicRenderModeCorrectionBoundary
    ; additiveEventFieldWitness = Event.scalarFieldSampleIsTen
    ; labelProductDistanceWitness = Labels.labelABDistanceIsTwo
    ; labelFactorIndependenceWitness =
        Labels.binaryDistanceCanVanishWhileHierarchyDiffers
    ; anisotropicRadiusWitness =
        Anisotropic.canonicalSquaredRadiusIsTwo
    ; finiteTubeQuadratureWitness =
        Anisotropic.canonicalTubeMassIsTen
    ; correctedSharpnessWitness = refl , refl
    ; temporalGraphForwardWitness = Event.edgeIsForwardByConstruction
    ; thresholdFiltrationWitness = Persistence.highIncludedInLow
    ; ridgeCodimensionWitness = Event.oneDimensionalRidgeInFourHasThreeNormals
    ; finiteFixedPointConvergenceWitness = Renderer.seedConvergesInTwoSteps
    ; finiteFixedPointUniquenessWitness = Renderer.fixedPointUnique
    ; commonAttenuationCancellationWitness =
        Renderer.uniformAttenuationCancelsFromComposition
    ; exactStraightAlphaWitness = Stability.canonicalCompositedAlpha
    ; legacyStraightAlphaRejected =
        RenderCorrection.legacyCodeIsNotExactAlphaNumerator
    ; cyclicAssociativityWitness = Carry.cyclicAdd3Associative
    ; cyclicInverseWitness = Cyclic.cyclicInverseRight
    ; carryResidualWitness = Carry.positiveOverflowLifts
    ; softOneHotExactnessWitness = Carry.basisConvolutionExact
    ; softCarryMassWitness = Soft.hardCarrySoftOutputHasUnitMass
    ; designationChoiceWitness =
        Soft.trueOnlyConsequenceIsVacuous ,
        Soft.neutralDesignatedConsequenceFails
    ; characterHomomorphismWitness = Cyclic.characterIsHomomorphism
    ; depthNineCountWitness = Padic.depthNineCountIs19683
    ; depthNineEmbeddingWitness = Padic.sampleDepthNineVoxel
    ; parentMassWitness = LOD.canonicalParentMassIsNine
    ; conditionalZoomWitness = Consistency.coarseExpectationRecoversParent
    ; unequalMassNormalisationWitness =
        Consistency.unequalMassNormalisationsDiffer
    ; prefixLocalConstancyWitness =
        Padic.kernelLocallyConstantOnDepthTwoCylinder
    ; addressRetentionWitness = Padic.canonicalFieldRetainsAddress
    ; eventPadicSourceCount = Sources.canonicalEventPadicSourceCountIsTen
    }
