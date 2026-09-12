module DASHI.Combinatorics.GraphColouringRecolourPantsSnowballExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Moonshine.JInvariantColourWheelNineSheetPantsGluingExact as Pants369

------------------------------------------------------------------------
-- GRAPH COLOURING / RECOLOURING / PANTS SNOWBALL
--
-- This owner is deliberately thin.  It does not reproduce either published
-- graph-theory proof.  It records exact source attribution, bounded claims,
-- QID/Dewey coordinates, and the concrete cross-pollination into the existing
-- 369 colour-wheel / nine-sheet / 27-voxel / ternary-pants carrier.
------------------------------------------------------------------------

data QidState : Set where
  qid : String → QidState
  unresolvedQid : QidState

record KnowledgeCoordinate : Set where
  constructor knowledgeCoordinate
  field
    label : String
    qidState : QidState
    deweyParent : String
    coordinateIsProof : Bool
    coordinateIsProofIsFalse : coordinateIsProof ≡ false

open KnowledgeCoordinate public

graphTheoryCoordinate : KnowledgeCoordinate
graphTheoryCoordinate =
  knowledgeCoordinate "graph theory" (qid "Q131476") "511.5" false refl

graphColouringCoordinate : KnowledgeCoordinate
graphColouringCoordinate =
  knowledgeCoordinate "graph coloring" (qid "Q504843") "511.5" false refl

fourColourTheoremCoordinate : KnowledgeCoordinate
fourColourTheoremCoordinate =
  knowledgeCoordinate "four color theorem" (qid "Q184410") "511.5" false refl

hedetniemiConjectureCoordinate : KnowledgeCoordinate
hedetniemiConjectureCoordinate =
  knowledgeCoordinate "Hedetniemi's conjecture" unresolvedQid "511.5" false refl

------------------------------------------------------------------------
-- Primary and secondary attribution.
------------------------------------------------------------------------

shitovPrimary : Source.AttributedSource
shitovPrimary =
  Source.mkDOISource
    "Yaroslav Shitov"
    "Counterexamples to Hedetniemi's conjecture"
    "Annals of Mathematics 190 (2019), no. 2, 663-667"
    "2019"
    "10.4007/annals.2019.190.2.6"
    "https://annals.math.princeton.edu/2019/190-2/p06"
    Source.academicArticleSource
    "primary source for the finite-simple-graph counterexample showing that chromatic number of a tensor product can be strictly smaller than the minimum chromatic number of its factors"
    Source.publicAttribution

shitovQuanta : Source.AttributedSource
shitovQuanta =
  Source.mkNoDOISource
    "Erica Klarreich"
    "A 53-Year-Old Network Coloring Conjecture Is Disproved"
    "Quanta Magazine"
    "2019"
    "https://www.quantamagazine.org/mathematician-disproves-hedetniemis-graph-theory-conjecture-20190617/"
    Source.newsSource
    "secondary explanatory source for Shitov's counterexample, tensor-product colour lift, exponential-graph construction, and historical context"
    Source.publicAttribution

fourColourPrimary : Source.AttributedSource
fourColourPrimary =
  Source.mkDOISource
    "Yuta Inoue; Ken-ichi Kawarabayashi; Atsuyuki Miyashita; Bojan Mohar; Carsten Thomassen; Mikkel Thorup"
    "The Four Color Theorem with Linearly Many Reducible Configurations and Near-Linear Time Coloring"
    "arXiv:2603.24880 [math.CO], version 2"
    "2026"
    "10.48550/arXiv.2603.24880"
    "https://arxiv.org/abs/2603.24880"
    Source.academicArticleSource
    "primary source for the theorem that planar triangulations contain linearly many pairwise non-touching reducible configurations or pairwise non-crossing obstructing cycles of length at most five, yielding O(n log n) 4-colouring"
    Source.publicAttribution

fourColourQuanta : Source.AttributedSource
fourColourQuanta =
  Source.mkNoDOISource
    "Gregory Barber"
    "The Four-Color Theorem Gets a Rare New Proof"
    "Quanta Magazine"
    "2026"
    "https://www.quantamagazine.org/the-four-color-theorem-gets-a-rare-new-proof-20260910/"
    Source.newsSource
    "secondary explanatory source for the new proof architecture, historical computer-assisted context, and interpretation of reductions in zero-curvature flat regions"
    Source.publicAttribution

graphColouringSourceAtlas : Source.AttributedSourceAtlas
graphColouringSourceAtlas =
  Source.mkSourceAtlas
    "graph colouring recolouring pants snowball source atlas"
    "DASHI.Combinatorics.GraphColouringRecolourPantsSnowballExact"
    (shitovPrimary ∷ shitovQuanta ∷ fourColourPrimary ∷ fourColourQuanta ∷ [])
    "attribution for the Shitov counterexample and the 2026 linearly-many-reductions Four-Color proof; source identity does not import either proof into DASHI"

------------------------------------------------------------------------
-- Typed paper claims.  These are proposition labels / provenance boundaries,
-- not imported mathematical proofs.
------------------------------------------------------------------------

data PaperClaim : Set where
  tensorProjectionColouringExists : PaperClaim
  hedetniemiUniversalEquality : PaperClaim
  finiteSimpleCounterexampleExists : PaperClaim
  singleReductionExists : PaperClaim
  linearManyRobustReductionsExist : PaperClaim
  zeroCurvatureRegionsCanCarryReductions : PaperClaim
  nearLinearFourColourAlgorithm : PaperClaim

data ClaimStatus : Set where
  sourceSupports : ClaimStatus
  sourceRefutes : ClaimStatus
  notReprovedHere : ClaimStatus

record AttributedClaim : Set where
  constructor attributedClaim
  field
    claim : PaperClaim
    status : ClaimStatus
    attribution : Source.AttributedSource
    dashProofImported : Bool
    dashProofImportedIsFalse : dashProofImported ≡ false

open AttributedClaim public

shitovCounterexampleClaim : AttributedClaim
shitovCounterexampleClaim =
  attributedClaim finiteSimpleCounterexampleExists sourceSupports shitovPrimary false refl

hedetniemiRefutedClaim : AttributedClaim
hedetniemiRefutedClaim =
  attributedClaim hedetniemiUniversalEquality sourceRefutes shitovPrimary false refl

fourColourLinearReductionClaim : AttributedClaim
fourColourLinearReductionClaim =
  attributedClaim linearManyRobustReductionsExist sourceSupports fourColourPrimary false refl

fourColourFlatReductionClaim : AttributedClaim
fourColourFlatReductionClaim =
  attributedClaim zeroCurvatureRegionsCanCarryReductions sourceSupports fourColourPrimary false refl

fourColourNearLinearClaim : AttributedClaim
fourColourNearLinearClaim =
  attributedClaim nearLinearFourColourAlgorithm sourceSupports fourColourPrimary false refl

------------------------------------------------------------------------
-- Four colours have three nonzero transition classes.
--
-- This is a structural bridge only.  The transition classes below are NOT
-- identified with Z/3Z, SSP trits, KernelTrit, or BranchSlot.
------------------------------------------------------------------------

data Bit : Set where
  b0 b1 : Bit

data Colour4 : Set where
  c00 c01 c10 c11 : Colour4

data NonzeroColourDifference : Set where
  d01 d10 d11 : NonzeroColourDifference

record FourColourTriadicBridgeBoundary : Set where
  constructor fourColourTriadicBridgeBoundary
  field
    fourVertexColours : Bool
    threeNonzeroDifferenceClasses : Bool
    threeDifferenceClassesAreZ3 : Bool
    threeDifferenceClassesAreKernelTrit : Bool
    colourIdentityIsVoxelIdentity : Bool

canonicalFourColourTriadicBridgeBoundary : FourColourTriadicBridgeBoundary
canonicalFourColourTriadicBridgeBoundary =
  fourColourTriadicBridgeBoundary true true false false false

------------------------------------------------------------------------
-- Existing 369 owner: do not rebuild the carrier.
------------------------------------------------------------------------

existingTwentySevenIsDepthThreePantsPath : Bool
existingTwentySevenIsDepthThreePantsPath =
  Pants369.ColourWheelNinePantsBoundary.twentySevenIsDepthThreePantsPath
    Pants369.canonicalColourWheelNinePantsBoundary

existingMobiusActsAsSeamFlip : Bool
existingMobiusActsAsSeamFlip =
  Pants369.ColourWheelNinePantsBoundary.mobiusActsAsSecondCoordinateSeamFlip
    Pants369.canonicalColourWheelNinePantsBoundary

existingFinitePathIsSmoothSurface : Bool
existingFinitePathIsSmoothSurface =
  Pants369.ColourWheelNinePantsBoundary.finitePantsPathIsSmoothPantsSurface
    Pants369.canonicalColourWheelNinePantsBoundary

------------------------------------------------------------------------
-- Recolouring snowball.
--
-- The target is not "colour = trit".  It is transport of a colouring state
-- across an already-typed reduction/gluing carrier, retaining the possibility
-- that a locally valid recolouring fails at a global seam.
------------------------------------------------------------------------

data RecolourStage : Set where
  localColourAssignment : RecolourStage
  localRecolourMove : RecolourStage
  boundaryRestriction : RecolourStage
  pantsSeamCompatibility : RecolourStage
  recursiveGluingCompatibility : RecolourStage
  reduction : RecolourStage
  backwardColourLift : RecolourStage
  globalColouring : RecolourStage

data SnowballRelation : Set where
  dependsOn : SnowballRelation
  generalisesTo : SnowballRelation
  supportedBy : SnowballRelation
  crossPollinatesWith : SnowballRelation

record SnowballEdge : Set where
  constructor snowballEdge
  field
    from : RecolourStage
    relation : SnowballRelation
    to : RecolourStage
    conclusionPaying : Bool

open SnowballEdge public

localMoveToBoundary : SnowballEdge
localMoveToBoundary =
  snowballEdge localRecolourMove dependsOn boundaryRestriction true

boundaryToSeam : SnowballEdge
boundaryToSeam =
  snowballEdge boundaryRestriction dependsOn pantsSeamCompatibility true

seamToRecursive : SnowballEdge
seamToRecursive =
  snowballEdge pantsSeamCompatibility dependsOn recursiveGluingCompatibility true

reductionToLift : SnowballEdge
reductionToLift =
  snowballEdge reduction dependsOn backwardColourLift true

liftToGlobal : SnowballEdge
liftToGlobal =
  snowballEdge backwardColourLift dependsOn globalColouring true

------------------------------------------------------------------------
-- Fail-closed conclusions.
------------------------------------------------------------------------

record GraphColouringPantsBoundary : Set where
  constructor graphColouringPantsBoundary
  field
    sourceAttributionRecorded : Bool
    qidAndDeweyCoordinatesRecorded : Bool
    qidAndDeweyAreProof : Bool
    shitovProofReproducedInKernel : Bool
    fourColourProofReproducedInKernel : Bool
    existing27VoxelPantsCarrierReused : Bool
    existingSeamFlipReusedAsRecolouringAnalogy : Bool
    localRecolourImpliesGlobalGluingCompatibility : Bool
    threeTransitionClassesIdentifiedWithZ3 : Bool
    reductionRequiresBackwardColourLift : Bool
    snowballAcquisitionMayProceedOutOfDependencyOrder : Bool
    snowballPaymentMayProceedOutOfDependencyOrder : Bool

canonicalGraphColouringPantsBoundary : GraphColouringPantsBoundary
canonicalGraphColouringPantsBoundary =
  graphColouringPantsBoundary
    true
    true
    false
    false
    false
    existingTwentySevenIsDepthThreePantsPath
    existingMobiusActsAsSeamFlip
    false
    false
    true
    true
    false
