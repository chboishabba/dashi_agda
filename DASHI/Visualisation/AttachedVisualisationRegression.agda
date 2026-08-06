module DASHI.Visualisation.AttachedVisualisationRegression where

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
import DASHI.Visualisation.AttachedVisualisationBoundary as Boundary

attachedVisualisationBoundaryExists :
  Boundary.AttachedVisualisationBoundary
attachedVisualisationBoundaryExists =
  Boundary.canonicalAttachedVisualisationBoundary

threeSaddleRegression :
  Junction.ordinarySaddleCount
    Junction.threeSimultaneousSaddles
  ≡
  3
threeSaddleRegression = refl

singleSaddleDisconnectedRegression :
  Junction.presentationConnectivity Junction.oneOrdinarySaddle
  ≡
  Junction.disconnectedPantsCylinder
singleSaddleDisconnectedRegression = refl

kernelEquivarianceRegression :
  Junction.triToBiKernel
    (Triadic.negateTrit Triadic.negativeTrit)
    (Triadic.negateTrit Triadic.negativeTrit)
    (Triadic.negateTrit Triadic.negativeTrit)
  ≡
  Triadic.negateNine
    (Junction.triToBiKernel
      Triadic.negativeTrit
      Triadic.negativeTrit
      Triadic.negativeTrit)
kernelEquivarianceRegression = refl

transportConservationRegression :
  Transport.routedMass
    Transport.tiltedRouting
    Transport.waistA
  +
  Transport.routedMass
    Transport.tiltedRouting
    Transport.waistB
  ≡
  6
transportConservationRegression = refl

phaseCancellationRegression :
  Phase.phaseResultToTrit
    (Phase.phaseResultant
      Phase.phaseZero
      Phase.phaseOne
      Phase.phaseTwo)
  ≡
  Triadic.zeroTrit
phaseCancellationRegression = refl

phaseRotationRegression :
  Phase.coupledPhaseJunction
    (Phase.rotatePhase Phase.phaseZero)
    (Phase.rotatePhase Phase.phaseZero)
    (Phase.rotatePhase Phase.phaseZero)
  ≡
  Phase.rotatePhaseOutput
    (Phase.coupledPhaseJunction
      Phase.phaseZero
      Phase.phaseZero
      Phase.phaseZero)
phaseRotationRegression = refl

planeReparameterisationRegression :
  Slice.slicePoint (Slice.swapBasis Slice.angledPlane) 2 3
  ≡
  Slice.slicePoint Slice.angledPlane 3 2
planeReparameterisationRegression =
  Slice.basisSwapReparameterises

simplexRegression :
  Colour.weightNumeratorTotal Colour.canonicalWeight
  ≡
  Colour.denominator Colour.canonicalWeight
simplexRegression = refl

commonPenaltyCancellationRegression :
  Colour.profileMixture Colour.baseProfile
  ≡
  Colour.profileMixture Colour.commonScaledProfile
commonPenaltyCancellationRegression =
  Colour.commonMultiplicativePenaltyCancelsFromMixture

tiePenaltySignRegression :
  Colour.legacySignedTieEffect Colour.smallGap
  ≡
  Colour.amplifiesActivity
tiePenaltySignRegression =
  Colour.legacyPositiveGapAmplifies

correctedTiePenaltyRegression :
  Colour.correctedNonnegativeTieEffect Colour.exactTie
  ≡
  Colour.suppressesActivity
correctedTiePenaltyRegression =
  Colour.correctedTieSuppresses

colourCollisionRegression :
  Colour.fixedColour Colour.classD
  ≡
  Colour.fixedColour Colour.classE
colourCollisionRegression =
  Colour.distinctClassesCollide

combinedObjectiveRegression :
  Objective.combinedObjective Objective.combinedWinner ≡ 79
combinedObjectiveRegression = Objective.combinedWinnerScore

compactObjectiveRegression :
  Objective.combinedObjective Search.compactIslandCandidate ≡ 33
compactObjectiveRegression = Objective.compactCombinedScore

simplexDisplayLossRegression :
  Diagnostics.unrepresentedSimplexDirections ≡ 1
simplexDisplayLossRegression =
  Diagnostics.oneSimplexDirectionIsDropped

pcaCollisionRegression :
  Diagnostics.projectMixture Diagnostics.mixtureA
  ≡
  Diagnostics.projectMixture Diagnostics.mixtureB
pcaCollisionRegression = Diagnostics.projectionCollision

int8RankingFailureRegression :
  Search.floatWinner ≡ Search.badQuantisedWinner → ⊥
int8RankingFailureRegression =
  Search.badWinnerDiffers

topTwoRecallRegression :
  Search.InShortlist Search.floatWinner Search.coarseProposal
topTwoRecallRegression =
  Search.trueWinnerSurvivesShortlist

quantisationStageRegression :
  Quantised.quantisedPath
    Quantised.quantisePreactivation
    Quantised.levelOne
  ≡
  Quantised.quantisedPath
    Quantised.quantiseActivation
    Quantised.levelOne
  →
  ⊥
quantisationStageRegression =
  Quantised.quantisationStagesCanDiffer

calibrationWinnerRegression :
  Quantised.sharedCalibrationWinner
  ≡
  Search.broadAngledCandidate
calibrationWinnerRegression = refl

lipschitzCellRegression :
  Quantised.cellUpperBoundScaled ≡ 18
lipschitzCellRegression = Quantised.cellUpperBoundIsEighteen

quadraticRegression :
  Parity.directSquaredDistance 2 3
  ≡
  Parity.quadraticSquaredDistance 2 3
quadraticRegression =
  Parity.quadraticPrecomputationSample

rendererParityRegression :
  Parity.optimisedRenderer Parity.mixedPixel
  ≡
  Parity.referenceRenderer Parity.mixedPixel
rendererParityRegression = refl

rendererReceiptRegression :
  Receipt.benchmarkExecuted Receipt.canonicalSourceReceipt ≡ false
rendererReceiptRegression =
  Receipt.sourceReceiptDoesNotClaimExecutedBenchmark

barEquivarianceRegression :
  Graph.renderBarMarks
    (Graph.swapBars (Graph.barDatum 3 4))
  ≡
  Graph.swapMarks
    (Graph.renderBarMarks (Graph.barDatum 3 4))
barEquivarianceRegression = refl

graphEnergyEquivarianceRegression :
  Graph.symmetricEnergy
    (Graph.swapLayout (Graph.layout2 2 3))
  ≡
  Graph.symmetricEnergy (Graph.layout2 2 3)
graphEnergyEquivarianceRegression =
  Graph.energyRelabellingEquivariantGeneric (Graph.layout2 2 3)

barAggregationCommutationRegression :
  Commutation.sourceBarAggregation (Graph.barDatum 3 4)
  ≡
  Commutation.visualBarAggregation
    (Graph.renderBarMarks (Graph.barDatum 3 4))
barAggregationCommutationRegression = refl

fieldMassRegression :
  Adapter.totalFieldMass
    (Adapter.convolveScaled
      (Adapter.extractMeasure Adapter.canonicalSource))
  ≡
  10
fieldMassRegression = refl

embeddingDependenceRegression :
  Commutation.fieldFromEmbedding Commutation.embeddingOne
  ≡
  Commutation.fieldFromEmbedding Commutation.embeddingTwo
  →
  ⊥
embeddingDependenceRegression =
  Commutation.nonRigidEmbeddingsChangeField

sourceCountRegression :
  Sources.canonicalAttachedVisualisationSourceCount ≡ 8
sourceCountRegression =
  Sources.canonicalAttachedVisualisationSourceCountIsEight
