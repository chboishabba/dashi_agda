module DASHI.Visualisation.AttachedVisualisationBoundary where

open import DASHI.Core.Prelude

import DASHI.Physics.Foundations.TriToBiSingularJunctionExact as Junction
import DASHI.Physics.Foundations.TriToBiTransportExact as Transport
import DASHI.Biology.TriadicKernelLiftQuotientExact as Triadic
import DASHI.Visualisation.AffinePlaneSliceExact as Slice
import DASHI.Visualisation.FiveClassSimplexColourExact as Colour
import DASHI.Visualisation.CoarseSliceSearchExact as Search
import DASHI.Visualisation.RendererParityExact as Parity
import DASHI.Visualisation.GraphSeriesSemanticExact as Graph
import DASHI.Visualisation.MeasureFieldAdapterExact as Adapter
import DASHI.Visualisation.AttachedVisualisationSourceAtlas as Sources

record AttachedVisualisationBoundary : Set where
  field
    triToBiJunctionBoundary :
      Junction.TriToBiSingularJunctionBoundary
    triToBiTransportBoundary :
      Transport.TriToBiTransportBoundary
    affinePlaneBoundary :
      Slice.AffinePlaneSliceBoundary
    fiveClassColourBoundary :
      Colour.FiveClassSimplexColourBoundary
    coarseSearchBoundary :
      Search.CoarseSliceSearchBoundary
    rendererParityBoundary :
      Parity.RendererParityBoundary
    graphSeriesBoundary :
      Graph.GraphSeriesSemanticBoundary
    adapterStageBoundary :
      Adapter.AdapterStageBoundary

    connectedJunctionSaddleCount :
      Junction.ordinarySaddleCount
        Junction.threeSimultaneousSaddles
      ≡
      3

    globalInvolutionWitness :
      ∀ x y z →
      Junction.triToBiKernel
        (Triadic.negateTrit x)
        (Triadic.negateTrit y)
        (Triadic.negateTrit z)
      ≡
      Triadic.negateNine
        (Junction.triToBiKernel x y z)

    conservativeRoutingWitness :
      Transport.routedMass
        Transport.balancedRouting
        Transport.waistA
      +
      Transport.routedMass
        Transport.balancedRouting
        Transport.waistB
      ≡
      6

    affineSliceWitness :
      Slice.slicePoint Slice.angledPlane 2 3
      ≡
      Slice.point4 2 3 3 6

    simplexClosureWitness :
      Colour.weightNumeratorTotal Colour.canonicalWeight
      ≡
      Colour.denominator Colour.canonicalWeight

    colourCollisionWitness :
      Colour.fixedColour Colour.classD
      ≡
      Colour.fixedColour Colour.classE

    correctedSearchWitness :
      Search.coverageAwareScore Search.coverageAwareWinner
      ≡
      22

    shortlistRecallWitness :
      Search.InShortlist Search.floatWinner Search.coarseProposal

    optimisedRendererWitness :
      ∀ input →
      Parity.optimisedRenderer input
      ≡
      Parity.referenceRenderer input

    graphEquivarianceWitness :
      ∀ datum →
      Graph.renderBarMarks (Graph.swapBars datum)
      ≡
      Graph.swapMarks (Graph.renderBarMarks datum)

    fieldMassWitness :
      Adapter.totalFieldMass
        (Adapter.convolveScaled
          (Adapter.extractMeasure Adapter.canonicalSource))
      ≡
      10

    attachedVisualisationSourceCount :
      Sources.canonicalAttachedVisualisationSourceCount ≡ 8

open AttachedVisualisationBoundary public

canonicalAttachedVisualisationBoundary :
  AttachedVisualisationBoundary
canonicalAttachedVisualisationBoundary =
  record
    { triToBiJunctionBoundary =
        Junction.canonicalTriToBiSingularJunctionBoundary
    ; triToBiTransportBoundary =
        Transport.canonicalTriToBiTransportBoundary
    ; affinePlaneBoundary =
        Slice.canonicalAffinePlaneSliceBoundary
    ; fiveClassColourBoundary =
        Colour.canonicalFiveClassSimplexColourBoundary
    ; coarseSearchBoundary =
        Search.canonicalCoarseSliceSearchBoundary
    ; rendererParityBoundary =
        Parity.canonicalRendererParityBoundary
    ; graphSeriesBoundary =
        Graph.canonicalGraphSeriesSemanticBoundary
    ; adapterStageBoundary =
        Adapter.canonicalAdapterStageBoundary
    ; connectedJunctionSaddleCount =
        Junction.connectedGenusZeroNeedsThreeSaddles
    ; globalInvolutionWitness =
        Junction.triToBiKernelEquivariant
    ; conservativeRoutingWitness =
        refl
    ; affineSliceWitness =
        Slice.angledSample
    ; simplexClosureWitness =
        Colour.canonicalWeightCloses
    ; colourCollisionWitness =
        Colour.distinctClassesCollide
    ; correctedSearchWitness =
        Search.coverageRepairRestoresBroadWinner
    ; shortlistRecallWitness =
        Search.trueWinnerSurvivesShortlist
    ; optimisedRendererWitness =
        Parity.optimisedParity
    ; graphEquivarianceWitness =
        Graph.barRelabellingEquivariant
    ; fieldMassWitness =
        refl
    ; attachedVisualisationSourceCount =
        Sources.canonicalAttachedVisualisationSourceCountIsEight
    }
