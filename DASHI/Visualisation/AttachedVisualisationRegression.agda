module DASHI.Visualisation.AttachedVisualisationRegression where

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

colourCollisionRegression :
  Colour.fixedColour Colour.classD
  ≡
  Colour.fixedColour Colour.classE
colourCollisionRegression =
  Colour.distinctClassesCollide

int8RankingFailureRegression :
  Search.floatWinner ≡ Search.badQuantisedWinner → ⊥
int8RankingFailureRegression =
  Search.badWinnerDiffers

topTwoRecallRegression :
  Search.InShortlist Search.floatWinner Search.coarseProposal
topTwoRecallRegression =
  Search.trueWinnerSurvivesShortlist

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

barEquivarianceRegression :
  Graph.renderBarMarks
    (Graph.swapBars (Graph.barDatum 3 4))
  ≡
  Graph.swapMarks
    (Graph.renderBarMarks (Graph.barDatum 3 4))
barEquivarianceRegression = refl

fieldMassRegression :
  Adapter.totalFieldMass
    (Adapter.convolveScaled
      (Adapter.extractMeasure Adapter.canonicalSource))
  ≡
  10
fieldMassRegression = refl

sourceCountRegression :
  Sources.canonicalAttachedVisualisationSourceCount ≡ 8
sourceCountRegression =
  Sources.canonicalAttachedVisualisationSourceCountIsEight
