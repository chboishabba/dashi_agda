module DASHI.Reasoning.TrialecticWeightedDirectedGraph369Exact where

------------------------------------------------------------------------
-- WEIGHTED DIRECTED MATRIX <-> THREE-VERTEX RELATIONAL GRAPH.
--
-- Source prompt: Tivadar Danka, "Matrices are graphs" illustration shared
-- 26 October 2026. The finite matrix/weighted-digraph correspondence is
-- standard linear algebra, not a theorem attributed to the illustration.
--
-- DASHI ownership: finite adapter, explicit 3-node example, C3
-- non-equivariance witness, and independent attached-face non-descent.
-- Reuse existing observer matrix, binary-in-ternary 369 address, attached
-- trialectic face, non-geometric response, typed hyperfabric and pants
-- authorization surfaces; do not construct parallel semantic owners.
--
-- Matrix convention: row = source vertex; column = target vertex.
-- Values are EXACT nonnegative integer weights in tenths, not floating
-- measurements.  In the example 5 denotes 0.5; 22 denotes 2.2.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Nat as BN using ()
import DASHI.Reasoning.TrialecticObserverMatrix369Exact as Observer
import DASHI.Reasoning.TrialecticBoundaryFaceNonfactorabilityExact as Face
import DASHI.Core.ConsumerDescentMinimalObserverExact as Descent
import DASHI.Core.ArgumentResponseNonGeometricOppositeBidiExact as Response
import DASHI.Core.McCallCategoryStrategyBoundaryExact as McCall
import DASHI.Reasoning.Trialectic369RubikRefinementExact as Rubik
import DASHI.Foundations.SSPTritCarrier as SSP
import DASHI.Reasoning.TypedHyperfabricCore as Hyperfabric
import DASHI.Reasoning.TypedHyperfabricPantsGluingBridgeExact as PantsBridge
open import Data.List using ([]; _∷_)
import DASHI.Combinatorics.GraphColouring369PantsHomomorphismBoundaryExact as ColourPants

WeightedMatrix3 : Set
WeightedMatrix3 = Observer.ObserverMatrix3 Nat

-- A directed binary edge has two endpoints in the existing ternary carrier.
-- The source/target direction is NOT geometric position, negation or parity.
WeightedDigraph3 : Set
WeightedDigraph3 =
  Observer.Participant3 -> Observer.Participant3 -> Nat

matrixToDigraph : WeightedMatrix3 -> WeightedDigraph3
matrixToDigraph = Observer.viewAt

digraphToMatrix : WeightedDigraph3 -> WeightedMatrix3
digraphToMatrix weight =
  Observer.observerMatrix3
    (weight Observer.participantA Observer.participantA)
    (weight Observer.participantA Observer.participantB)
    (weight Observer.participantA Observer.participantC)
    (weight Observer.participantB Observer.participantA)
    (weight Observer.participantB Observer.participantB)
    (weight Observer.participantB Observer.participantC)
    (weight Observer.participantC Observer.participantA)
    (weight Observer.participantC Observer.participantB)
    (weight Observer.participantC Observer.participantC)

matrixDigraphRoundTrip :
  (matrix : WeightedMatrix3) ->
  digraphToMatrix (matrixToDigraph matrix) ≡ matrix
matrixDigraphRoundTrip
  (Observer.observerMatrix3 aa ab ac ba bb bc ca cb cc) = refl

digraphMatrixRoundTrip :
  (weight : WeightedDigraph3) ->
  (source target : Observer.Participant3) ->
  matrixToDigraph (digraphToMatrix weight) source target
  ≡ weight source target
digraphMatrixRoundTrip weight Observer.participantA Observer.participantA = refl
digraphMatrixRoundTrip weight Observer.participantA Observer.participantB = refl
digraphMatrixRoundTrip weight Observer.participantA Observer.participantC = refl
digraphMatrixRoundTrip weight Observer.participantB Observer.participantA = refl
digraphMatrixRoundTrip weight Observer.participantB Observer.participantB = refl
digraphMatrixRoundTrip weight Observer.participantB Observer.participantC = refl
digraphMatrixRoundTrip weight Observer.participantC Observer.participantA = refl
digraphMatrixRoundTrip weight Observer.participantC Observer.participantB = refl
digraphMatrixRoundTrip weight Observer.participantC Observer.participantC = refl

-- From the supplied image; integer-tenths representation is exact.
dankaWeightedMatrixTenths : WeightedMatrix3
dankaWeightedMatrixTenths =
  Observer.observerMatrix3
    5 10 0
    2 0 22
    18 20 0

dankaWeight : WeightedDigraph3
dankaWeight = matrixToDigraph dankaWeightedMatrixTenths

-- Nonzero entries encode arrows, zero entries encode absent arrows.
presentWeight : Nat -> Bool
presentWeight BN.zero = false
presentWeight (BN.suc _) = true

presentEdge :
  Observer.Participant3 -> Observer.Participant3 -> Bool
presentEdge source target = presentWeight (dankaWeight source target)

edgeCount : Bool -> Nat
edgeCount true = 1
edgeCount false = 0

nonzeroEdgeCount : Nat
nonzeroEdgeCount =
  edgeCount (presentEdge Observer.participantA Observer.participantA)
  + edgeCount (presentEdge Observer.participantA Observer.participantB)
  + edgeCount (presentEdge Observer.participantA Observer.participantC)
  + edgeCount (presentEdge Observer.participantB Observer.participantA)
  + edgeCount (presentEdge Observer.participantB Observer.participantB)
  + edgeCount (presentEdge Observer.participantB Observer.participantC)
  + edgeCount (presentEdge Observer.participantC Observer.participantA)
  + edgeCount (presentEdge Observer.participantC Observer.participantB)
  + edgeCount (presentEdge Observer.participantC Observer.participantC)

sixArrowsIncludingOneLoop : nonzeroEdgeCount ≡ 6
sixArrowsIncludingOneLoop = refl

missingAtoC : presentEdge Observer.participantA Observer.participantC ≡ false
missingAtoC = refl

presentCtoA : presentEdge Observer.participantC Observer.participantA ≡ true
presentCtoA = refl

-- Reversing an edge is a well-typed operation but does NOT preserve weight.
reverseEdgeDoesNotPreserveWeight :
  dankaWeight Observer.participantA Observer.participantB
  ≡ dankaWeight Observer.participantB Observer.participantA -> ⊥
reverseEdgeDoesNotPreserveWeight ()

------------------------------------------------------------------------
-- The three vertex LABELS support a C3 permutation; this weighted graph
-- does not carry that permutation as a weighted graph automorphism.
------------------------------------------------------------------------

rotateVertex : Observer.Participant3 -> Observer.Participant3
rotateVertex Observer.participantA = Observer.participantB
rotateVertex Observer.participantB = Observer.participantC
rotateVertex Observer.participantC = Observer.participantA

rotateVertexCubed :
  (vertex : Observer.Participant3) ->
  rotateVertex (rotateVertex (rotateVertex vertex)) ≡ vertex
rotateVertexCubed Observer.participantA = refl
rotateVertexCubed Observer.participantB = refl
rotateVertexCubed Observer.participantC = refl

-- If the graph were C3 invariant, its A-loop of weight 5 would equal
-- the B-loop of weight 0.  This is a finite counterexample.
weightedDankaGraphNotC3Invariant :
  ((source target : Observer.Participant3) ->
    dankaWeight (rotateVertex source) (rotateVertex target)
    ≡ dankaWeight source target) -> ⊥
weightedDankaGraphNotC3Invariant invariant with
  invariant Observer.participantA Observer.participantA
... | ()

------------------------------------------------------------------------
-- Extra triadic data does not descend from even the FULL weighted 3x3.
-- Existing non-descent machinery supplies the proof, not a new axiom.
------------------------------------------------------------------------

record GraphWithAttachedFace : Set where
  constructor graph-with-attached-face
  field
    graphMatrix : WeightedMatrix3
    attachedFace : Face.TriadicFaceRelation

open GraphWithAttachedFace public

graphObserver : GraphWithAttachedFace -> WeightedMatrix3
graphObserver = graphMatrix

triadicConsumer : GraphWithAttachedFace -> Face.TriadicFaceRelation
triadicConsumer = attachedFace

sameMatrixReciprocal : GraphWithAttachedFace
sameMatrixReciprocal =
  graph-with-attached-face dankaWeightedMatrixTenths Face.reciprocalFace

sameMatrixCoercive : GraphWithAttachedFace
sameMatrixCoercive =
  graph-with-attached-face dankaWeightedMatrixTenths Face.coerciveFace

sameMatrixDifferentFace :
  graphObserver sameMatrixReciprocal ≡ graphObserver sameMatrixCoercive
sameMatrixDifferentFace = refl

faceDifference :
  triadicConsumer sameMatrixReciprocal
  ≡ triadicConsumer sameMatrixCoercive -> ⊥
faceDifference ()

graphAttachedFaceNonDescent :
  Descent.ConsumerNonDescentWitness graphObserver triadicConsumer
graphAttachedFaceNonDescent =
  Descent.consumerNonDescentWitness
    sameMatrixReciprocal
    sameMatrixCoercive
    sameMatrixDifferentFace
    faceDifference

matrixDoesNotDetermineTrialecticFace :
  Descent.FactorsThrough graphObserver triadicConsumer -> ⊥
matrixDoesNotDetermineTrialecticFace =
  Descent.nonDescentWitnessBlocksFactorization graphAttachedFaceNonDescent

------------------------------------------------------------------------
-- Existing 369 trit-address chart is a SEPARATE value-typed chart.  A
-- weight 22 is not definitionally an SSP trit.  Equal nine-position
-- indexing alone does not create a lossless weight-to-trit codec.
------------------------------------------------------------------------

ternaryNinePositionChartRoundTrip :
  (coded : Observer.ObserverMatrix3 SSP.SSPTrit) ->
  Rubik.depth3AddressToObserver (Rubik.observerToDepth3Address coded)
  ≡ coded
ternaryNinePositionChartRoundTrip = Rubik.observerAddressRoundTrip

argumentResponseIsNotAutomaticallyNegation :
  Response.ResponseIsLogicalNegation -> ⊥
argumentResponseIsNotAutomaticallyNegation =
  Response.responseIsNotAutomaticallyLogicalNegation

intersectionalStrategyRechartStillRequired :
  McCall.CategoryStrategyBoundary.strategyTranslationRequiresExplicitWitness
    McCall.canonicalCategoryStrategyBoundary ≡ true
intersectionalStrategyRechartStillRequired =
  McCall.strategyTranslationRequiresExplicitWitnessIsTrue
    McCall.canonicalCategoryStrategyBoundary

hyperfabricCompatibilityStillRequired :
  Hyperfabric.TypedHyperfabricAuthorityBoundary.globalSectionRequiresCompatibilityWitness
    Hyperfabric.canonicalTypedHyperfabricAuthorityBoundary ≡ true
hyperfabricCompatibilityStillRequired = refl

pantsAdjacencyNotCreatedByWeightedThreeGraph :
  ColourPants.GraphColouring369PantsBoundary.carrierRoundTripUpgradedToGraphIsomorphism
    ColourPants.canonicalGraphColouring369PantsBoundary ≡ false
pantsAdjacencyNotCreatedByWeightedThreeGraph = refl

record WeightedGraphTrialectic369Boundary : Set where
  constructor weighted-graph-trialectic-369-boundary
  field
    directedMatrixGraphChartReversible : Bool
    sixNonzeroDirectedArcs : Bool
    labelledVertexC3OrderThree : Bool
    suppliedWeightsC3Invariant : Bool
    reverseEdgeEqualsLogicalNegation : Bool
    graphDeterminesAttachedTriadicFace : Bool
    sourceTargetPairIsNinePositionChart : Bool
    ninePositionsAutomaticallyEncodeWeightsAsTrits : Bool
    independentHyperfabricAndPantsGluingRequired : Bool

canonicalWeightedGraphTrialectic369Boundary :
  WeightedGraphTrialectic369Boundary
canonicalWeightedGraphTrialectic369Boundary =
  weighted-graph-trialectic-369-boundary
    true true true false false false true false true

------------------------------------------------------------------------
-- Follow-on: matrix multiplication is the total weight of length-2 walks.
-- The missing direct A -> C arc does not block a mediated A -> B -> C walk.
-- This exact finite example is compatible with the existing Balaban finite
-- local-walk machinery; it is NOT a new semigroup/locality theorem.
------------------------------------------------------------------------

twoStepWeightAtoC : Nat
twoStepWeightAtoC =
  dankaWeight Observer.participantA Observer.participantA
  * dankaWeight Observer.participantA Observer.participantC
  + dankaWeight Observer.participantA Observer.participantB
  * dankaWeight Observer.participantB Observer.participantC
  + dankaWeight Observer.participantA Observer.participantC
  * dankaWeight Observer.participantC Observer.participantC

twoStepAtoCEquals220Hundredths :
  twoStepWeightAtoC ≡ 220
twoStepAtoCEquals220Hundredths = refl

twoStepAtoCNotZero : twoStepWeightAtoC ≡ 0 -> ⊥
twoStepAtoCNotZero ()

------------------------------------------------------------------------
-- A nontrivial instantiated compatible hyperfabric section. Vertex stalks
-- store complete outgoing weight rows; edge stalks store the selected weight.
-- Incidence is source-directed only.  No source authority, psychology,
-- universal directed sheaf, pants topology or smoothness is inferred.
------------------------------------------------------------------------

data OrderedEdge : Set where
  orderedEdge : Observer.Participant3 -> Observer.Participant3 -> OrderedEdge

data OutgoingIncidence : Observer.Participant3 -> OrderedEdge -> Set where
  outgoingIncidence :
    ∀ {source target} ->
    OutgoingIncidence source (orderedEdge source target)

restrictOutgoing :
  ∀ {vertex edge} ->
  OutgoingIncidence vertex edge ->
  (Observer.Participant3 -> Nat) ->
  Nat
restrictOutgoing (outgoingIncidence {target = target}) row = row target

outgoingWeightFabric :
  Hyperfabric.TypedHyperfabric Observer.Participant3 OrderedEdge
outgoingWeightFabric = record
  { vertexStalk = λ _ -> Observer.Participant3 -> Nat
  ; edgeStalk = λ _ -> Nat
  ; incidence = OutgoingIncidence
  ; restrict = restrictOutgoing
  ; edgeProvenance =
      λ _ -> "source: supplied 26 Oct 2026 matrix illustration" ∷ []
  ; edgeSalience =
      λ { (orderedEdge source target) -> dankaWeight source target }
  ; fabricLabel = "three-node directed weighted graph; outgoing-row stalks"
  }

outgoingWeightSection :
  Hyperfabric.GlobalSection outgoingWeightFabric
outgoingWeightSection = record
  { vertexValue = dankaWeight
  ; edgeValue =
      λ { (orderedEdge source target) -> dankaWeight source target }
  ; compatible =
      λ { (outgoingIncidence {source = source} {target = target}) -> refl }
  ; sectionReceipt =
      "outgoing edge restrictions recover exactly the source-row weights"
  }

-- A pants channel interpretation plus interface match must be supplied
-- separately.  Naming the exact existing obligation does not inhabit it.
DirectedGraphPantsGluingObligation : Set₁
DirectedGraphPantsGluingObligation =
  PantsBridge.HyperfabricPantsGluing outgoingWeightSection
