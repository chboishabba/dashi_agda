module DASHI.Visualisation.AttachedVisualisationBoundary where

open import DASHI.Core.Prelude

import DASHI.Physics.Foundations.TriToBiSingularJunctionExact as Junction
import DASHI.Physics.Foundations.TriToBiTransportExact as Transport
import DASHI.Physics.Foundations.TriToBiPhaseDialecticExact as Phase
import DASHI.Biology.TriadicKernelLiftQuotientExact as Triadic
import DASHI.Visualisation.AffinePlaneSliceExact as Slice
import DASHI.Visualisation.FiveClassSimplexColourExact as Colour
import DASHI.Visualisation.SliceObjectiveExact as Objective
import DASHI.Visualisation.ColourProjectionDiagnosticsExact as Diagnostics
import DASHI.Visualisation.CoarseSliceSearchExact as Search
import DASHI.Visualisation.QuantisedSearchBoundsExact as Quantised
import DASHI.Visualisation.RendererParityExact as Parity
import DASHI.Visualisation.RendererReceiptExact as Receipt
import DASHI.Visualisation.GraphSeriesSemanticExact as Graph
import DASHI.Visualisation.MeasureFieldAdapterExact as Adapter
import DASHI.Visualisation.AdapterCommutationExact as Commutation
import DASHI.Visualisation.AttachedVisualisationSourceAtlas as Sources

record AttachedVisualisationBoundary : Set where
  field
    triToBiJunctionBoundary :
      Junction.TriToBiSingularJunctionBoundary
    triToBiTransportBoundary :
      Transport.TriToBiTransportBoundary
    triToBiPhaseDialecticBoundary :
      Phase.TriToBiPhaseDialecticBoundary
    affinePlaneBoundary :
      Slice.AffinePlaneSliceBoundary
    fiveClassColourBoundary :
      Colour.FiveClassSimplexColourBoundary
    sliceObjectiveBoundary :
      Objective.SliceObjectiveBoundary
    colourProjectionDiagnosticsBoundary :
      Diagnostics.ColourProjectionDiagnosticsBoundary
    coarseSearchBoundary :
      Search.CoarseSliceSearchBoundary
    quantisedSearchBoundary :
      Quantised.QuantisedSearchBoundsBoundary
    rendererParityBoundary :
      Parity.RendererParityBoundary
    rendererReceiptBoundary :
      Receipt.RendererReceiptBoundary
    graphSeriesBoundary :
      Graph.GraphSeriesSemanticBoundary
    adapterStageBoundary :
      Adapter.AdapterStageBoundary
    adapterCommutationBoundary :
      Commutation.AdapterCommutationBoundary

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

    phaseCancellationWitness :
      Phase.phaseResultToTrit
        (Phase.phaseResultant
          Phase.phaseZero
          Phase.phaseOne
          Phase.phaseTwo)
      ≡
      Triadic.zeroTrit

    dialecticalResidualWitness :
      Phase.inputJointQuantity
      ≡
      Phase.outputJointQuantity
      +
      Phase.junctionDialecticalResidual

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

    combinedObjectiveWitness :
      Objective.combinedObjective Objective.combinedWinner
      ≡
      79

    droppedDirectionWitness :
      Diagnostics.unrepresentedSimplexDirections ≡ 1

    correctedSearchWitness :
      Search.coverageAwareScore Search.coverageAwareWinner
      ≡
      22

    shortlistRecallWitness :
      Search.InShortlist Search.floatWinner Search.coarseProposal

    sharedCalibrationWinnerWitness :
      Quantised.sharedCalibrationWinner
      ≡
      Search.broadAngledCandidate

    quantisedTopThreeRetainsWinner :
      Quantised.Proposed Search.floatWinner Quantised.allThreeCandidates

    optimisedRendererWitness :
      ∀ input →
      Parity.optimisedRenderer input
      ≡
      Parity.referenceRenderer input

    sourceReceiptDoesNotClaimBenchmark :
      Receipt.benchmarkExecuted Receipt.canonicalSourceReceipt ≡ false

    graphEquivarianceWitness :
      ∀ datum →
      Graph.renderBarMarks (Graph.swapBars datum)
      ≡
      Graph.swapMarks (Graph.renderBarMarks datum)

    barAggregationCommutationWitness :
      ∀ datum →
      Commutation.sourceBarAggregation datum
      ≡
      Commutation.visualBarAggregation
        (Graph.renderBarMarks datum)

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
    ; triToBiPhaseDialecticBoundary =
        Phase.canonicalTriToBiPhaseDialecticBoundary
    ; affinePlaneBoundary =
        Slice.canonicalAffinePlaneSliceBoundary
    ; fiveClassColourBoundary =
        Colour.canonicalFiveClassSimplexColourBoundary
    ; sliceObjectiveBoundary =
        Objective.canonicalSliceObjectiveBoundary
    ; colourProjectionDiagnosticsBoundary =
        Diagnostics.canonicalColourProjectionDiagnosticsBoundary
    ; coarseSearchBoundary =
        Search.canonicalCoarseSliceSearchBoundary
    ; quantisedSearchBoundary =
        Quantised.canonicalQuantisedSearchBoundsBoundary
    ; rendererParityBoundary =
        Parity.canonicalRendererParityBoundary
    ; rendererReceiptBoundary =
        Receipt.canonicalRendererReceiptBoundary
    ; graphSeriesBoundary =
        Graph.canonicalGraphSeriesSemanticBoundary
    ; adapterStageBoundary =
        Adapter.canonicalAdapterStageBoundary
    ; adapterCommutationBoundary =
        Commutation.canonicalAdapterCommutationBoundary
    ; connectedJunctionSaddleCount =
        Junction.connectedGenusZeroNeedsThreeSaddles
    ; globalInvolutionWitness =
        Junction.triToBiKernelEquivariant
    ; conservativeRoutingWitness =
        refl
    ; phaseCancellationWitness =
        Phase.cancellationMapsToTernaryNeutral
    ; dialecticalResidualWitness =
        Phase.jointInvariantWithResidual
    ; affineSliceWitness =
        Slice.angledSample
    ; simplexClosureWitness =
        Colour.canonicalWeightCloses
    ; colourCollisionWitness =
        Colour.distinctClassesCollide
    ; combinedObjectiveWitness =
        Objective.combinedWinnerScore
    ; droppedDirectionWitness =
        Diagnostics.oneSimplexDirectionIsDropped
    ; correctedSearchWitness =
        Search.coverageRepairRestoresBroadWinner
    ; shortlistRecallWitness =
        Search.trueWinnerSurvivesShortlist
    ; sharedCalibrationWinnerWitness =
        refl
    ; quantisedTopThreeRetainsWinner =
        Quantised.floatWinnerRetained
    ; optimisedRendererWitness =
        Parity.optimisedParity
    ; sourceReceiptDoesNotClaimBenchmark =
        Receipt.sourceReceiptDoesNotClaimExecutedBenchmark
    ; graphEquivarianceWitness =
        Graph.barRelabellingEquivariant
    ; barAggregationCommutationWitness =
        Commutation.barAggregationCommutation
    ; fieldMassWitness =
        refl
    ; attachedVisualisationSourceCount =
        Sources.canonicalAttachedVisualisationSourceCountIsEight
    }
