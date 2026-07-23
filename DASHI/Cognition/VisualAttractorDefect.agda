module DASHI.Cognition.VisualAttractorDefect where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)

import DASHI.Cognition.Base369ZeroFibre as Fibre
import DASHI.Cognition.CognitiveResearchSources as Sources
import DASHI.Cognition.VisualPatternGeneratorMDL as Visual

------------------------------------------------------------------------
-- Research contact.
--
-- G. Bard Ermentrout and Jack D. Cowan (1979),
-- "A mathematical theory of visual hallucination patterns",
-- DOI 10.1007/BF00336965.
--
-- Paul C. Bressloff, Jack D. Cowan, Martin Golubitsky, Peter J. Thomas and
-- Matthew C. Wiener (2001),
-- "Geometric visual hallucinations, Euclidean symmetry and the functional
-- architecture of striate cortex", DOI 10.1098/rstb.2000.0769.
--
-- The finite DASHI scores below are not fits to those papers.  They encode the
-- structural intersection suggested by neural-field pattern formation:
-- geometric mode + dynamical stability + low description length.
------------------------------------------------------------------------

visualFieldSources : List Sources.ResearchSource
visualFieldSources =
  Sources.ermentroutCowanHallucinationPatterns ∷
  Sources.bressloffGeometricHallucinations ∷
  Sources.carhartHarrisLSDNeuroimaging ∷ []

------------------------------------------------------------------------
-- Basis + noise + defect decomposition.
------------------------------------------------------------------------

record VisualDecomposition : Set where
  constructor visualDecomposition
  field
    basisGenerator : Visual.VisualGenerator
    basisCost      : Nat
    noiseCost      : Nat
    defectCost     : Nat

open VisualDecomposition public

totalVisualCost : VisualDecomposition → Nat
totalVisualCost decomposition =
  basisCost decomposition +
  noiseCost decomposition +
  defectCost decomposition

canonicalDecomposition : Visual.VisualGenerator → VisualDecomposition
canonicalDecomposition Visual.orientationWave =
  visualDecomposition Visual.orientationWave 2 0 1
canonicalDecomposition Visual.lattice =
  visualDecomposition Visual.lattice 3 0 1
canonicalDecomposition Visual.checker =
  visualDecomposition Visual.checker 3 0 1
canonicalDecomposition Visual.spiral =
  visualDecomposition Visual.spiral 4 1 1
canonicalDecomposition Visual.tunnel =
  visualDecomposition Visual.tunnel 4 1 1
canonicalDecomposition Visual.cobweb =
  visualDecomposition Visual.cobweb 4 1 1
canonicalDecomposition Visual.semanticScene =
  visualDecomposition Visual.semanticScene 9 3 6

latticeTotalCostIsFour :
  totalVisualCost (canonicalDecomposition Visual.lattice) ≡ 4
latticeTotalCostIsFour = refl

semanticTotalCostIsEighteen :
  totalVisualCost (canonicalDecomposition Visual.semanticScene) ≡ 18
semanticTotalCostIsEighteen = refl

------------------------------------------------------------------------
-- Finite neural-field mode surface.
--
-- eigenDefect = residual from a selected linear mode;
-- nonlinearDefect = residual after nonlinear saturation/selection;
-- semanticDefect = additional high-level binding cost.
------------------------------------------------------------------------

record ModeReceipt (generator : Visual.VisualGenerator) : Set where
  constructor modeReceipt
  field
    eigenDefect      : Nat
    nonlinearDefect  : Nat
    semanticDefect   : Nat
    symmetrySupported : Bool

open ModeReceipt public

modeReceiptFor : (generator : Visual.VisualGenerator) → ModeReceipt generator
modeReceiptFor Visual.orientationWave = modeReceipt 0 1 0 true
modeReceiptFor Visual.lattice = modeReceipt 0 1 0 true
modeReceiptFor Visual.checker = modeReceipt 0 1 0 true
modeReceiptFor Visual.spiral = modeReceipt 1 1 0 true
modeReceiptFor Visual.tunnel = modeReceipt 1 1 0 true
modeReceiptFor Visual.cobweb = modeReceipt 1 1 0 true
modeReceiptFor Visual.semanticScene = modeReceipt 3 3 6 false

modeDefect : ∀ {generator} → ModeReceipt generator → Nat
modeDefect receipt =
  eigenDefect receipt + nonlinearDefect receipt + semanticDefect receipt

compressionAttractorScore : Visual.VisualGenerator → Nat
compressionAttractorScore generator =
  Visual.visualMDL generator 0 + modeDefect (modeReceiptFor generator)

latticeAttractorScoreIsFour :
  compressionAttractorScore Visual.lattice ≡ 4
latticeAttractorScoreIsFour = refl

semanticAttractorScoreIsTwentySeven :
  compressionAttractorScore Visual.semanticScene ≡ 27
semanticAttractorScoreIsTwentySeven = refl

atMost : Nat → Nat → Bool
atMost zero limit = true
atMost (suc actual) zero = false
atMost (suc actual) (suc limit) = atMost actual limit

latticeBeatsSemanticByJointScore :
  atMost
    (compressionAttractorScore Visual.lattice)
    (compressionAttractorScore Visual.semanticScene)
  ≡ true
latticeBeatsSemanticByJointScore = refl

record TripleAttractorWitness (generator : Visual.VisualGenerator) : Set where
  constructor tripleAttractorWitness
  field
    neuralAttractor       : Bool
    geometricEigenmode    : Bool
    mdlCompressionAttractor : Bool

latticeTripleIntersection : TripleAttractorWitness Visual.lattice
latticeTripleIntersection = tripleAttractorWitness true true true

------------------------------------------------------------------------
-- Almost-binary visual lane.
--
-- Holding the public ternary coordinate at zero leaves the two-state
-- orientation fibre of the six-carrier visible.  This is a finite mechanism
-- for alternating edge/polarity patterns within a ternary architecture.
------------------------------------------------------------------------

record ZeroOrientationPixel : Set where
  constructor zeroOrientationPixel
  field
    hiddenOrientation : Fibre.Orientation

blackLikePixel : ZeroOrientationPixel
blackLikePixel = zeroOrientationPixel Fibre.forward

whiteLikePixel : ZeroOrientationPixel
whiteLikePixel = zeroOrientationPixel Fibre.reverse

alternateOrientation : ZeroOrientationPixel → ZeroOrientationPixel
alternateOrientation (zeroOrientationPixel Fibre.forward) = whiteLikePixel
alternateOrientation (zeroOrientationPixel Fibre.reverse) = blackLikePixel

alternateTwiceReturns : (pixel : ZeroOrientationPixel) →
  alternateOrientation (alternateOrientation pixel) ≡ pixel
alternateTwiceReturns (zeroOrientationPixel Fibre.forward) = refl
alternateTwiceReturns (zeroOrientationPixel Fibre.reverse) = refl

------------------------------------------------------------------------
-- Authority boundary: these are finite generator and defect laws, not a claim
-- that one score is a measured cortical energy or that all psychedelic imagery
-- is exhausted by V1 form constants.
------------------------------------------------------------------------

record VisualAuthorityBoundary : Set where
  constructor visualAuthorityBoundary
  field
    neuralFieldMotivationSourced : Bool
    finiteGeneratorScoresProved  : Bool
    measuredCorticalEnergyBound  : Bool
    allHallucinationsExplained   : Bool

canonicalVisualAuthorityBoundary : VisualAuthorityBoundary
canonicalVisualAuthorityBoundary =
  visualAuthorityBoundary true true false false
