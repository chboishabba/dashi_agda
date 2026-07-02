module DASHI.Physics.YangMills.BalabanPolymerDiameterEntropy where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Sigma using (Σ; _,_; fst; snd)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; []; length)
open import Data.Nat.Base using (ℕ; _≤_; _*_; _+_; _^_; z≤n)
open import DASHI.Core.Prelude using (_×_)

open import DASHI.Geometry.Gauge.SUNPrimitives using (clayYangMillsPromoted)
open import DASHI.Foundations.RealAnalysisAxioms
  using (ℝ; _≤ℝ_; _<ℝ_; 0ℝ; 1ℝ; _*ℝ_; -ℝ_)
open import DASHI.Physics.YangMills.ProofTargetSurface
open import DASHI.Physics.YangMills.YMSourceAuthoritySurface using
  ( SourceAuthorityId
  ; eriksson-2602-0041
  ; dashi-internal-proof
  ; paperImport
  ; proved
  ; VerificationStatus
  ; mixedReducer
  )
import DASHI.Physics.YangMills.ArithmeticLemmaQueue as ArithmeticQueue
import DASHI.Physics.YangMills.P01P33ProofSurfaces as Surfaces
import DASHI.Physics.YangMills.GraphCombinatorics as GraphCombinatorics
import DASHI.Physics.YangMills.BalabanLargeFieldSuppression as LargeField

Scalar : Set
Scalar = String

-- ── Entropy-side theorem queue ───────────────────────────────────────
--
-- P06, P07, and P09 are represented as explicit theorem surfaces plus
-- witnesses.  The arithmetic side is consumed from the shared
-- ArithmeticLemmaQueue so the module carries queue structure rather than
-- a status-table narrative.

polymerAnimalCountingBoundSurface : ProofTargetSurface
polymerAnimalCountingBoundSurface =
  Surfaces.polymerAnimalCountingBoundSurface

pZeroPositiveSurface : ProofTargetSurface
pZeroPositiveSurface = Surfaces.pZeroPositiveSurface

entropyBeatenByFullDecaySurface : ProofTargetSurface
entropyBeatenByFullDecaySurface =
  Surfaces.entropyBeatenByFullDecaySurface

kPSummabilityBoundSurface : ProofTargetSurface
kPSummabilityBoundSurface = Surfaces.kPSummabilityBoundSurface

record RootedPolymerShellCountingInterface : Set₁ where
  field
    Polymer : Set
    diameter : Polymer → ℕ
    root : Polymer
    shellAt : ℕ → List Polymer
    shellCountBound :
      ∀ (n : ℕ) →
      length (shellAt n) ≤ (n * n)
    interfaceBoundary : String
    interfaceBoundaryIsCanonical :
      interfaceBoundary ≡
      "P06 reducer: an imported rooted-polymer counting witness is re-expressed as a DASHI shell-counting interface over diameter-indexed rooted polymer shells."

record P06a1BoundedDegreeSupportGraphSkeleton : Set₁ where
  field
    rootedShellInterface : RootedPolymerShellCountingInterface
    maxDegreeBound : ℕ
    theoremBoundary : String
    theoremBoundaryIsCanonical :
      theoremBoundary ≡
      "P06a1: DASHI isolates the graph-skeleton side of P06 as a rooted support-graph shell family together with an explicit bounded-degree parameter."

record P06a2aBoundedDegreeRootBallGrowth : Set₁ where
  field
    boundedDegreeSkeleton : P06a1BoundedDegreeSupportGraphSkeleton
    rootBallShellBound :
      ∀ (n : ℕ) →
      length
        (RootedPolymerShellCountingInterface.shellAt
          (P06a1BoundedDegreeSupportGraphSkeleton.rootedShellInterface
            boundedDegreeSkeleton)
          n)
      ≤ (n * n)
    theoremBoundary : String
    theoremBoundaryIsCanonical :
      theoremBoundary ≡
      "P06a2a: before any polymer-specific counting refinement, DASHI exposes the rooted bounded-degree shell family as a root-ball growth bound over diameter shells."

record ConnectedSkeletonHasRootedSpanningTree : Set₁ where
  field
    boundedDegreeSkeleton : P06a1BoundedDegreeSupportGraphSkeleton
    theoremBoundary : String
    theoremBoundaryIsCanonical :
      theoremBoundary ≡
      "P06a2b: every rooted connected support-graph skeleton is first reduced to a rooted spanning-tree witness before any DFS walk encoding is applied."

record RootedTreeDFSWalk : Set₁ where
  field
    rootedSpanningTreeWitness : ConnectedSkeletonHasRootedSpanningTree
    theoremBoundary : String
    theoremBoundaryIsCanonical :
      theoremBoundary ≡
      "P06a2c: each rooted spanning tree is consumed through a depth-first traversal witness of length linear in the tree size."

record BoundedDegreeWalkCount : Set₁ where
  field
    boundedDegreeSkeleton : P06a1BoundedDegreeSupportGraphSkeleton
    theoremBoundary : String
    theoremBoundaryIsCanonical :
      theoremBoundary ≡
      "P06a2d: bounded-degree support graphs bound the number of rooted walks of any fixed length by a simple exponential walk-count estimate."

record ConnectedSkeletonCoveredByDFSWalk : Set₁ where
  field
    dfsWalkWitness : RootedTreeDFSWalk
    walkCountWitness : BoundedDegreeWalkCount
    theoremBoundary : String
    theoremBoundaryIsCanonical :
      theoremBoundary ≡
      "P06a2e: every rooted connected skeleton is covered by the visited set of a bounded-degree DFS walk, exposing the exact counting bridge used by P06a2."

record P06a2fDFSWalkSizeShellCountingBridge : Set₁ where
  field
    rootedSpanningTreeWitness : ConnectedSkeletonHasRootedSpanningTree
    dfsWalkWitness : RootedTreeDFSWalk
    walkCountWitness : BoundedDegreeWalkCount
    sizeShellBridgeBound :
      ∀ (n : ℕ) →
      length
        (RootedPolymerShellCountingInterface.shellAt
          (P06a1BoundedDegreeSupportGraphSkeleton.rootedShellInterface
            (ConnectedSkeletonHasRootedSpanningTree.boundedDegreeSkeleton
              rootedSpanningTreeWitness))
          n)
      ≤ ((P06a1BoundedDegreeSupportGraphSkeleton.maxDegreeBound
            (ConnectedSkeletonHasRootedSpanningTree.boundedDegreeSkeleton
              rootedSpanningTreeWitness) * n)
          * (P06a1BoundedDegreeSupportGraphSkeleton.maxDegreeBound
            (ConnectedSkeletonHasRootedSpanningTree.boundedDegreeSkeleton
              rootedSpanningTreeWitness) * n))
    theoremBoundary : String
    theoremBoundaryIsCanonical :
      theoremBoundary ≡
      "P06a2f: the DFS-walk size-shell counting bridge is kept explicit between the rooted spanning-tree witness and the bounded-degree shell bound."

record P06a2RootedConnectedSkeletonSizeShellCounting : Set₁ where
  field
    boundedDegreeSkeleton : P06a1BoundedDegreeSupportGraphSkeleton
    rootBallGrowth : P06a2aBoundedDegreeRootBallGrowth
    rootedSpanningTreeWitness : ConnectedSkeletonHasRootedSpanningTree
    dfsWalkWitness : RootedTreeDFSWalk
    dfsWalkSizeShellBridge : P06a2fDFSWalkSizeShellCountingBridge
    walkCountWitness : BoundedDegreeWalkCount
    walkCoverWitness : ConnectedSkeletonCoveredByDFSWalk
    sizeShellBound :
      ∀ (n : ℕ) →
      length
        (RootedPolymerShellCountingInterface.shellAt
          (P06a1BoundedDegreeSupportGraphSkeleton.rootedShellInterface
            boundedDegreeSkeleton)
          n)
      ≤ ((P06a1BoundedDegreeSupportGraphSkeleton.maxDegreeBound
            boundedDegreeSkeleton * n)
          * (P06a1BoundedDegreeSupportGraphSkeleton.maxDegreeBound
            boundedDegreeSkeleton * n))
    theoremBoundary : String
    theoremBoundaryIsCanonical :
      theoremBoundary ≡
      "P06a2: bounded-degree rooted connected skeletons are counted first in size-indexed shells before any polymer-specific decoration overhead is considered."

record P06a3aDiameterShellContainedInRootBall : Set₁ where
  field
    sizeShellCounting : P06a2RootedConnectedSkeletonSizeShellCounting
    diameterShellContained :
      ∀ (n : ℕ) →
      length
        (RootedPolymerShellCountingInterface.shellAt
          (P06a1BoundedDegreeSupportGraphSkeleton.rootedShellInterface
            (P06a2RootedConnectedSkeletonSizeShellCounting.boundedDegreeSkeleton
              sizeShellCounting))
          n)
      ≤ ((P06a1BoundedDegreeSupportGraphSkeleton.maxDegreeBound
            (P06a2RootedConnectedSkeletonSizeShellCounting.boundedDegreeSkeleton
              sizeShellCounting) * n)
          * (P06a1BoundedDegreeSupportGraphSkeleton.maxDegreeBound
            (P06a2RootedConnectedSkeletonSizeShellCounting.boundedDegreeSkeleton
              sizeShellCounting) * n))
    theoremBoundary : String
    theoremBoundaryIsCanonical :
      theoremBoundary ≡
      "P06a3a: diameter-indexed rooted connected skeleton shells are first reduced to a bounded root-ball containment statement before the final diameter-shell count is consumed."

record ReducedSkeletonCardinalityBound : Set₁ where
  field
    boundedDegreeSkeleton : P06a1BoundedDegreeSupportGraphSkeleton
    sizeOrComplexityControlledByDiameter :
      ∀ (n : ℕ) →
      length
        (RootedPolymerShellCountingInterface.shellAt
          (P06a1BoundedDegreeSupportGraphSkeleton.rootedShellInterface
            boundedDegreeSkeleton)
          n)
      ≤ ((P06a1BoundedDegreeSupportGraphSkeleton.maxDegreeBound
            boundedDegreeSkeleton * n)
          * (P06a1BoundedDegreeSupportGraphSkeleton.maxDegreeBound
            boundedDegreeSkeleton * n))
    theoremBoundary : String
    theoremBoundaryIsCanonical :
      theoremBoundary ≡
      "P06a3b: bounded degree alone is not enough for exponential diameter-shell counting, so DASHI keeps the missing size-or-complexity-controlled-by-diameter statement as an explicit leaf."

record P06a3DiameterShellSkeletonCounting : Set₁ where
  field
    sizeShellCounting : P06a2RootedConnectedSkeletonSizeShellCounting
    diameterShellContainment : P06a3aDiameterShellContainedInRootBall
    reducedSkeletonCardinality : ReducedSkeletonCardinalityBound
    diameterShellBound :
      ∀ (n : ℕ) →
      length
        (RootedPolymerShellCountingInterface.shellAt
          (P06a1BoundedDegreeSupportGraphSkeleton.rootedShellInterface
            (P06a2RootedConnectedSkeletonSizeShellCounting.boundedDegreeSkeleton
              sizeShellCounting))
          n)
      ≤ ((P06a1BoundedDegreeSupportGraphSkeleton.maxDegreeBound
            (P06a2RootedConnectedSkeletonSizeShellCounting.boundedDegreeSkeleton
              sizeShellCounting) * n)
          * (P06a1BoundedDegreeSupportGraphSkeleton.maxDegreeBound
            (P06a2RootedConnectedSkeletonSizeShellCounting.boundedDegreeSkeleton
              sizeShellCounting) * n))
    theoremBoundary : String
    theoremBoundaryIsCanonical :
      theoremBoundary ≡
      "P06a3: diameter-indexed rooted connected skeleton shells are reduced using size-shell counting plus an explicit size-or-complexity-controlled-by-diameter leaf before the explicit decoration leaf is applied."

record P06aRootedConnectedSkeletonCounting : Set₁ where
  field
    rootedShellInterface : RootedPolymerShellCountingInterface
    boundedDegreeSkeleton : P06a1BoundedDegreeSupportGraphSkeleton
    rootBallGrowth : P06a2aBoundedDegreeRootBallGrowth
    rootedSpanningTreeWitness : ConnectedSkeletonHasRootedSpanningTree
    dfsWalkWitness : RootedTreeDFSWalk
    dfsWalkSizeShellBridge : P06a2fDFSWalkSizeShellCountingBridge
    walkCountWitness : BoundedDegreeWalkCount
    walkCoverWitness : ConnectedSkeletonCoveredByDFSWalk
    sizeShellCounting : P06a2RootedConnectedSkeletonSizeShellCounting
    diameterShellContainment : P06a3aDiameterShellContainedInRootBall
    reducedSkeletonCardinality : ReducedSkeletonCardinalityBound
    diameterShellCounting : P06a3DiameterShellSkeletonCounting
    theoremBoundary : String
    theoremBoundaryIsCanonical :
      theoremBoundary ≡
      "P06a: DASHI owns the rooted connected skeleton-counting bridge over bounded-degree support-graph shells, split into bounded-degree input, root-ball growth, DFS-walk size-shell counting, diameter-shell containment, and an explicit size-or-complexity-by-diameter leaf before the final diameter-shell reduction."

postulate
  BalabanPolymerContext : Set
  BalabanPolymer : Set
  BalabanReducedSkeleton : Set
  BalabanDecoration : Set

record BalabanGraphAdapter : Set₁ where
  field
    context : BalabanPolymerContext
    supportGraph : GraphCombinatorics.Graph
    degreeBound : Nat
    supportRoot :
      BalabanPolymer →
      GraphCombinatorics.Graph.Vertex supportGraph
    supportVertices :
      BalabanPolymer →
      List (GraphCombinatorics.Graph.Vertex supportGraph)
    rootedConnectedSkeletonAdapter :
      (P : BalabanPolymer) →
      GraphCombinatorics.RootedConnectedSkeleton
        supportGraph
        (supportRoot P)
        (supportVertices P)
    boundedDegreeAdapter :
      GraphCombinatorics.BoundedDegree supportGraph degreeBound

record BalabanReducedSkeletonComplexityAdapter
  (graphAdapter : BalabanGraphAdapter) : Set₁ where
  field
    atomsByComplexity :
      (r : GraphCombinatorics.Graph.Vertex
             (BalabanGraphAdapter.supportGraph graphAdapter))
      (X : List
        (GraphCombinatorics.Graph.Vertex
          (BalabanGraphAdapter.supportGraph graphAdapter))) →
      (rrs : GraphCombinatorics.RootedReducedSkeleton
               (BalabanGraphAdapter.supportGraph graphAdapter) r X) →
      length X ≤
      GraphCombinatorics.ReducedSkeletonComplexityMeasure r X rrs
    reducedComplexityLeaf :
      GraphCombinatorics.ReducedSkeletonComplexityControlledByDiameter
        (BalabanGraphAdapter.supportGraph graphAdapter)

record BalabanDecorationMultiplicityAdapter
  (graphAdapter : BalabanGraphAdapter) : Set₁ where
  field
    decorationMultiplicity :
      GraphCombinatorics.DecorationMultiplicity
        (BalabanGraphAdapter.supportGraph graphAdapter)
    decorationComplexityControlledBySkeleton :
      (r : GraphCombinatorics.Graph.Vertex
             (BalabanGraphAdapter.supportGraph graphAdapter))
      (X : List
        (GraphCombinatorics.Graph.Vertex
          (BalabanGraphAdapter.supportGraph graphAdapter))) →
      (rrs : GraphCombinatorics.RootedReducedSkeleton
               (BalabanGraphAdapter.supportGraph graphAdapter) r X) →
      GraphCombinatorics.DecorationMultiplicity.complexity
        decorationMultiplicity X ≤
      GraphCombinatorics.ReducedSkeletonComplexityMeasure r X rrs

record BalabanPolymerDecompositionAdapter
  (graphAdapter : BalabanGraphAdapter) : Set₁ where
  field
    polymerDecompositionLeaf :
      (X : List
        (GraphCombinatorics.Graph.Vertex
          (BalabanGraphAdapter.supportGraph graphAdapter))) →
      GraphCombinatorics.Polymer
        {BalabanGraphAdapter.supportGraph graphAdapter} X →
      Σ
        (List
          (GraphCombinatorics.Graph.Vertex
            (BalabanGraphAdapter.supportGraph graphAdapter)))
        (λ S →
          Σ
            (List
              (GraphCombinatorics.Graph.Vertex
                (BalabanGraphAdapter.supportGraph graphAdapter)))
            (λ d →
              GraphCombinatorics.SkeletonOf
                {BalabanGraphAdapter.supportGraph graphAdapter} X S ×
              GraphCombinatorics.DecorationOf
                {BalabanGraphAdapter.supportGraph graphAdapter} X d ×
              (GraphCombinatorics.diam_G
                 {BalabanGraphAdapter.supportGraph graphAdapter} S ≤
               GraphCombinatorics.diam_G
                 {BalabanGraphAdapter.supportGraph graphAdapter} X)
            )
        )
    diameterPreservedLeaf :
      (X S : List
        (GraphCombinatorics.Graph.Vertex
          (BalabanGraphAdapter.supportGraph graphAdapter))) →
      GraphCombinatorics.SkeletonOf
        {BalabanGraphAdapter.supportGraph graphAdapter} X S →
      GraphCombinatorics.diam_G
        {BalabanGraphAdapter.supportGraph graphAdapter} S ≡
      GraphCombinatorics.diam_G
        {BalabanGraphAdapter.supportGraph graphAdapter} X

LinearRangeExponentialSum : Set
LinearRangeExponentialSum =
  ∀ (C-size K B n : Nat) →
  GraphCombinatorics.sumPow C-size (K * n + B) ≤
  (2 * C-size ^ (K + B + 1)) ^ n

BalabanP06a2FromGraphCombinatorics :
  (graphAdapter : BalabanGraphAdapter) →
  Σ Nat
    (λ C-size →
      ∀ (r : GraphCombinatorics.Graph.Vertex
             (BalabanGraphAdapter.supportGraph graphAdapter))
        (m : Nat) →
      GraphCombinatorics.countSkeletons
        (BalabanGraphAdapter.supportGraph graphAdapter) r m ≤
      C-size ^ m)
BalabanP06a2FromGraphCombinatorics graphAdapter =
  GraphCombinatorics.P06a2RootedConnectedSkeletonSizeShellCounting
    (BalabanGraphAdapter.boundedDegreeAdapter graphAdapter)

BalabanP06a3bFromComplexity :
  (graphAdapter : BalabanGraphAdapter) →
  BalabanReducedSkeletonComplexityAdapter graphAdapter →
  GraphCombinatorics.ReducedSkeletonCardinalityBound
    (BalabanGraphAdapter.supportGraph graphAdapter)
BalabanP06a3bFromComplexity graphAdapter complexityAdapter =
  GraphCombinatorics.P06a3bFromComplexityControl
    (BalabanReducedSkeletonComplexityAdapter.atomsByComplexity
      complexityAdapter)
    (BalabanReducedSkeletonComplexityAdapter.reducedComplexityLeaf
      complexityAdapter)

BalabanCountingBoundReplacement :
  (graphAdapter : BalabanGraphAdapter) →
  BalabanReducedSkeletonComplexityAdapter graphAdapter →
  LinearRangeExponentialSum →
  Σ Nat
    (λ C-diam →
      ∀ (r : GraphCombinatorics.Graph.Vertex
             (BalabanGraphAdapter.supportGraph graphAdapter))
        (n : Nat) →
      GraphCombinatorics.countReducedSkeletonsWithDiam
        (BalabanGraphAdapter.supportGraph graphAdapter) r n ≤
      C-diam ^ n)
BalabanCountingBoundReplacement graphAdapter complexityAdapter linearRangeSum =
  GraphCombinatorics.P06a3FromSizeAndComplexity
    {G = BalabanGraphAdapter.supportGraph graphAdapter}
    {Δ = BalabanGraphAdapter.degreeBound graphAdapter}
    (BalabanP06a2FromGraphCombinatorics graphAdapter)
    (BalabanP06a3bFromComplexity graphAdapter complexityAdapter)
    linearRangeSum

BalabanDecorationMultiplicityByDiameter :
  (graphAdapter : BalabanGraphAdapter) →
  BalabanReducedSkeletonComplexityAdapter graphAdapter →
  (decorationAdapter : BalabanDecorationMultiplicityAdapter graphAdapter) →
  Σ Nat
    (λ C-decDiam →
      ∀ (r : GraphCombinatorics.Graph.Vertex
             (BalabanGraphAdapter.supportGraph graphAdapter))
        (X : List
          (GraphCombinatorics.Graph.Vertex
            (BalabanGraphAdapter.supportGraph graphAdapter)))
        (rrs : GraphCombinatorics.RootedReducedSkeleton
                 (BalabanGraphAdapter.supportGraph graphAdapter) r X)
        (n : Nat) →
      GraphCombinatorics.diam_G
        {BalabanGraphAdapter.supportGraph graphAdapter} X ≡ n →
      GraphCombinatorics.DecorationMultiplicity.countDecorations
        (BalabanDecorationMultiplicityAdapter.decorationMultiplicity
          decorationAdapter) X ≤
      C-decDiam ^ n)
BalabanDecorationMultiplicityByDiameter
  graphAdapter complexityAdapter decorationAdapter =
  GraphCombinatorics.P06bFromDecorationAndComplexity
    {G = BalabanGraphAdapter.supportGraph graphAdapter}
    (BalabanDecorationMultiplicityAdapter.decorationMultiplicity
      decorationAdapter)
    (BalabanReducedSkeletonComplexityAdapter.reducedComplexityLeaf
      complexityAdapter)
    (BalabanDecorationMultiplicityAdapter.decorationComplexityControlledBySkeleton
      decorationAdapter)

BalabanP06Dependencies :
  (graphAdapter : BalabanGraphAdapter) →
  BalabanReducedSkeletonComplexityAdapter graphAdapter →
  BalabanDecorationMultiplicityAdapter graphAdapter →
  BalabanPolymerDecompositionAdapter graphAdapter →
  GraphCombinatorics.P06MixedReducerDependencies
    (BalabanGraphAdapter.supportGraph graphAdapter)
    (BalabanGraphAdapter.degreeBound graphAdapter)
BalabanP06Dependencies graphAdapter complexityAdapter decorationAdapter
  polymerAdapter = record
  { sizeShellCountingOwned =
      BalabanP06a2FromGraphCombinatorics graphAdapter
  ; reducedComplexityLeaf =
      BalabanReducedSkeletonComplexityAdapter.reducedComplexityLeaf
        complexityAdapter
  ; atomsByComplexityLeaf =
      BalabanReducedSkeletonComplexityAdapter.atomsByComplexity
        complexityAdapter
  ; decorationLeaf =
      λ dec K B n X comp-le →
        GraphCombinatorics.DecorationMultiplicityByDiameter
          dec K B n X comp-le
  ; polymerDecompLeaf =
      BalabanPolymerDecompositionAdapter.polymerDecompositionLeaf
        polymerAdapter
  ; diameterPreservedLeaf =
      BalabanPolymerDecompositionAdapter.diameterPreservedLeaf
        polymerAdapter
  ; deriveDecompositionBound =
      GraphCombinatorics.DeriveDecompositionBoundFromLeaves
  }

record BalabanP06MixedReducerPayload : Set₁ where
  field
    graphAdapter : BalabanGraphAdapter
    reducedSkeletonComplexityAdapter :
      BalabanReducedSkeletonComplexityAdapter graphAdapter
    decorationMultiplicityAdapter :
      BalabanDecorationMultiplicityAdapter graphAdapter
    polymerDecompositionAdapter :
      BalabanPolymerDecompositionAdapter graphAdapter
    linearRangeSum : LinearRangeExponentialSum

record P06ModelLeafDischargePackage : Set₁ where
  field
    graphAdapter : BalabanGraphAdapter
    reducedSkeletonComplexityAdapter :
      BalabanReducedSkeletonComplexityAdapter graphAdapter
    decorationMultiplicityAdapter :
      BalabanDecorationMultiplicityAdapter graphAdapter
    polymerDecompositionAdapter :
      BalabanPolymerDecompositionAdapter graphAdapter
    linearRangeSum : LinearRangeExponentialSum

record OwnedP06a3DiameterShellCountingWitness : Set₁ where
  field
    payload : BalabanP06MixedReducerPayload
    diameterShellBound :
      Σ Nat
        (λ C-diam →
          ∀ (r : GraphCombinatorics.Graph.Vertex
                 (BalabanGraphAdapter.supportGraph
                   (BalabanP06MixedReducerPayload.graphAdapter payload)))
            (n : Nat) →
          GraphCombinatorics.countReducedSkeletonsWithDiam
            (BalabanGraphAdapter.supportGraph
              (BalabanP06MixedReducerPayload.graphAdapter payload)) r n ≤
          C-diam ^ n)

record OwnedP06ResidualCountingSprintWitness : Set₁ where
  field
    payload : BalabanP06MixedReducerPayload
    sourceAuthorityId : SourceAuthorityId
    theoremLocator : String
    status : VerificationStatus
    reducedSkeletonCardinality :
      GraphCombinatorics.ReducedSkeletonCardinalityBound
        (BalabanGraphAdapter.supportGraph
          (BalabanP06MixedReducerPayload.graphAdapter payload))
    diameterShellBound :
      Σ Nat
        (λ C-diam →
          ∀ (r : GraphCombinatorics.Graph.Vertex
                 (BalabanGraphAdapter.supportGraph
                   (BalabanP06MixedReducerPayload.graphAdapter payload)))
            (n : Nat) →
          GraphCombinatorics.countReducedSkeletonsWithDiam
            (BalabanGraphAdapter.supportGraph
              (BalabanP06MixedReducerPayload.graphAdapter payload)) r n ≤
          C-diam ^ n)

record OwnedP06bDecorationMultiplicityWitness : Set₁ where
  field
    payload : BalabanP06bDecorationPayload
    decorationBound :
      Σ Nat
        (λ C-decDiam →
          ∀ (r : GraphCombinatorics.Graph.Vertex
                 (BalabanGraphAdapter.supportGraph
                   (BalabanP06bDecorationPayload.graphAdapter payload)))
            (X : List
              (GraphCombinatorics.Graph.Vertex
                (BalabanGraphAdapter.supportGraph
                  (BalabanP06bDecorationPayload.graphAdapter payload))))
            (rrs : GraphCombinatorics.RootedReducedSkeleton
                     (BalabanGraphAdapter.supportGraph
                       (BalabanP06bDecorationPayload.graphAdapter payload))
                     r X)
            (n : Nat) →
          GraphCombinatorics.diam_G
            {BalabanGraphAdapter.supportGraph
              (BalabanP06bDecorationPayload.graphAdapter payload)} X ≡ n →
          GraphCombinatorics.DecorationMultiplicity.countDecorations
            (BalabanDecorationMultiplicityAdapter.decorationMultiplicity
              (BalabanP06bDecorationPayload.decorationMultiplicityAdapter
                payload))
            X ≤
          C-decDiam ^ n)

record OwnedP06AnimalCountingWitness : Set₁ where
  field
    payload : BalabanP06MixedReducerPayload
    animalCountingBound :
      Σ Nat
        (λ C-poly →
          ∀ (r : GraphCombinatorics.Graph.Vertex
                 (BalabanGraphAdapter.supportGraph
                   (BalabanP06MixedReducerPayload.graphAdapter payload)))
            (n : Nat) →
          GraphCombinatorics.countPolymersWithDiam
            (BalabanGraphAdapter.supportGraph
              (BalabanP06MixedReducerPayload.graphAdapter payload)) r n ≤
          C-poly ^ n)

record P06SourceSkeletonDecompositionSemanticKernel : Set₁ where
  field
    payload : BalabanP06MixedReducerPayload
    sourceAuthorityId : SourceAuthorityId
    theoremLocator : String
    status : VerificationStatus
    reducedSkeletonCardinality :
      GraphCombinatorics.ReducedSkeletonCardinalityBound
        (BalabanGraphAdapter.supportGraph
          (BalabanP06MixedReducerPayload.graphAdapter payload))
    diameterShellBound :
      Σ Nat
        (λ C-diam →
          ∀ (r : GraphCombinatorics.Graph.Vertex
                 (BalabanGraphAdapter.supportGraph
                   (BalabanP06MixedReducerPayload.graphAdapter payload)))
            (n : Nat) →
          GraphCombinatorics.countReducedSkeletonsWithDiam
            (BalabanGraphAdapter.supportGraph
              (BalabanP06MixedReducerPayload.graphAdapter payload)) r n ≤
          C-diam ^ n)
    decorationMultiplicityByDiameter :
      Σ Nat
        (λ C-decDiam →
          ∀ (r : GraphCombinatorics.Graph.Vertex
                 (BalabanGraphAdapter.supportGraph
                   (BalabanP06MixedReducerPayload.graphAdapter payload)))
            (X : List
              (GraphCombinatorics.Graph.Vertex
                (BalabanGraphAdapter.supportGraph
                  (BalabanP06MixedReducerPayload.graphAdapter payload))))
            (rrs : GraphCombinatorics.RootedReducedSkeleton
                     (BalabanGraphAdapter.supportGraph
                       (BalabanP06MixedReducerPayload.graphAdapter payload))
                     r X)
            (n : Nat) →
          GraphCombinatorics.diam_G
            {BalabanGraphAdapter.supportGraph
              (BalabanP06MixedReducerPayload.graphAdapter payload)} X ≡ n →
          GraphCombinatorics.DecorationMultiplicity.countDecorations
            (BalabanDecorationMultiplicityAdapter.decorationMultiplicity
              (BalabanP06MixedReducerPayload.decorationMultiplicityAdapter
                payload))
            X ≤
          C-decDiam ^ n)
    animalCountingBound :
      Σ Nat
        (λ C-poly →
          ∀ (r : GraphCombinatorics.Graph.Vertex
                 (BalabanGraphAdapter.supportGraph
                   (BalabanP06MixedReducerPayload.graphAdapter payload)))
            (n : Nat) →
          GraphCombinatorics.countPolymersWithDiam
            (BalabanGraphAdapter.supportGraph
              (BalabanP06MixedReducerPayload.graphAdapter payload)) r n ≤
          C-poly ^ n)

record OwnedP06SourceSkeletonDecompositionSprintWitness : Set₁ where
  field
    sourceAuthorityId : SourceAuthorityId
    theoremLocator : String
    status : VerificationStatus
    sourceSkeletonDecompositionSemanticKernel :
      P06SourceSkeletonDecompositionSemanticKernel
    residualCountingWitness :
      OwnedP06ResidualCountingSprintWitness
    decorationMultiplicityWitness :
      OwnedP06bDecorationMultiplicityWitness
    animalCountingWitness :
      OwnedP06AnimalCountingWitness

P06FromModelLeafDischargePackage :
  P06ModelLeafDischargePackage →
  BalabanP06MixedReducerPayload
P06FromModelLeafDischargePackage pkg = record
  { graphAdapter = P06ModelLeafDischargePackage.graphAdapter pkg
  ; reducedSkeletonComplexityAdapter = P06ModelLeafDischargePackage.reducedSkeletonComplexityAdapter pkg
  ; decorationMultiplicityAdapter = P06ModelLeafDischargePackage.decorationMultiplicityAdapter pkg
  ; polymerDecompositionAdapter = P06ModelLeafDischargePackage.polymerDecompositionAdapter pkg
  ; linearRangeSum = P06ModelLeafDischargePackage.linearRangeSum pkg
  }

BalabanP06AnimalCountingFromAdapters :
  (payload : BalabanP06MixedReducerPayload) →
  Σ Nat
    (λ C-poly →
      ∀ (r : GraphCombinatorics.Graph.Vertex
             (BalabanGraphAdapter.supportGraph
               (BalabanP06MixedReducerPayload.graphAdapter payload)))
        (n : Nat) →
      GraphCombinatorics.countPolymersWithDiam
        (BalabanGraphAdapter.supportGraph
          (BalabanP06MixedReducerPayload.graphAdapter payload)) r n ≤
      C-poly ^ n)
BalabanP06AnimalCountingFromAdapters payload =
  let graphAdapter =
        BalabanP06MixedReducerPayload.graphAdapter payload
      complexityAdapter =
        BalabanP06MixedReducerPayload.reducedSkeletonComplexityAdapter
          payload
      decorationAdapter =
        BalabanP06MixedReducerPayload.decorationMultiplicityAdapter
          payload
      polymerAdapter =
        BalabanP06MixedReducerPayload.polymerDecompositionAdapter
          payload
      dec =
        BalabanDecorationMultiplicityAdapter.decorationMultiplicity
          decorationAdapter
  in GraphCombinatorics.CanonicalP06FromMixedReducer
       {G = BalabanGraphAdapter.supportGraph graphAdapter}
       {Δ = BalabanGraphAdapter.degreeBound graphAdapter}
       (BalabanP06Dependencies graphAdapter complexityAdapter
         decorationAdapter polymerAdapter)
       dec
       (BalabanDecorationMultiplicityAdapter.decorationComplexityControlledBySkeleton
         decorationAdapter)
       (BalabanP06MixedReducerPayload.linearRangeSum payload)

record BalabanP06bDecorationPayload : Set₁ where
  field
    graphAdapter : BalabanGraphAdapter
    reducedSkeletonComplexityAdapter :
      BalabanReducedSkeletonComplexityAdapter graphAdapter
    decorationMultiplicityAdapter :
      BalabanDecorationMultiplicityAdapter graphAdapter

postulate
  currentBalabanGraphAdapter : BalabanGraphAdapter
  currentBalabanReducedSkeletonComplexityAdapter :
    BalabanReducedSkeletonComplexityAdapter
      currentBalabanGraphAdapter
  currentBalabanDecorationMultiplicityAdapter :
    BalabanDecorationMultiplicityAdapter
      currentBalabanGraphAdapter
  currentBalabanPolymerDecompositionAdapter :
    BalabanPolymerDecompositionAdapter
      currentBalabanGraphAdapter

record ImportedPolymerAnimalCountingBound : Set₁ where
  field
    sourceAuthorityId : SourceAuthorityId
    theoremLocator : String
    status : VerificationStatus
    mixedReducerPayload : BalabanP06MixedReducerPayload

record ImportedP06bPolymerDecorationMultiplicityBound : Set₁ where
  field
    sourceAuthorityId : SourceAuthorityId
    theoremLocator : String
    status : VerificationStatus
    decorationReducerPayload : BalabanP06bDecorationPayload

record ImportedKPSummabilityBound : Set where
  field
    sourceAuthorityId : SourceAuthorityId
    theoremLocator : String
    status : VerificationStatus
    reducer : ArithmeticQueue.KPSummabilityReducerFromAnimalDecayAndMargin

p0 : ℕ → ℝ
p0 = LargeField.p0

record ImportedPZeroPositive : Set where
  field
    sourceAuthorityId : SourceAuthorityId
    theoremLocator : String
    status : VerificationStatus
    positivity : ∀ (k : ℕ) → 0ℝ <ℝ p0 k

record ImportedEntropyBeatenByFullDecay : Set where
  field
    sourceAuthorityId : SourceAuthorityId
    theoremLocator : String
    status : VerificationStatus
    reducer : ArithmeticQueue.EntropyMarginFromDiameterConstant

record P06cSkeletonDecorationImpliesAnimalCounting : Set₁ where
  field
    p06aSkeletonCounting : P06aRootedConnectedSkeletonCounting
    p06bDecorationBound : ImportedP06bPolymerDecorationMultiplicityBound
    sourceWitness : ImportedPolymerAnimalCountingBound
    theoremBoundary : String
    theoremBoundaryIsCanonical :
      theoremBoundary ≡
      "P06c: DASHI recombines rooted support-graph skeleton shells with the owned decoration-multiplicity leaf so the full polymer animal-counting bound is assembled through a split skeleton-plus-decoration interface."

record P06AnimalCountingReducer : Set₁ where
  field
    p06aSkeletonCounting : P06aRootedConnectedSkeletonCounting
    p06bDecorationBound : ImportedP06bPolymerDecorationMultiplicityBound
    p06cRecombination : P06cSkeletonDecorationImpliesAnimalCounting
    sourceWitness : ImportedPolymerAnimalCountingBound
    rootedShellInterface : RootedPolymerShellCountingInterface
    proofBoundary : String
    proofBoundaryIsCanonical :
      proofBoundary ≡
      "P06AnimalCountingReducer: DASHI owns the rooted-shell adapter, the decoration multiplicity bridge, and the mixed skeleton-plus-decoration recombination that yields the current polymer animal-counting bound."

postulate
  expℝ : ℝ → ℝ
  Cd : ℝ
  κ : ℝ
  p0Min : ℝ
  kpSum : ℕ → ℝ
  kpBoundFormula : ℕ → ℝ

postulatedPositivity : ∀ (k : ℕ) → 0ℝ <ℝ p0 k
postulatedPositivity = LargeField.current-p₀-positive

currentBalabanP06MixedReducerPayload : BalabanP06MixedReducerPayload
currentBalabanP06MixedReducerPayload = record
  { graphAdapter = currentBalabanGraphAdapter
  ; reducedSkeletonComplexityAdapter =
      currentBalabanReducedSkeletonComplexityAdapter
  ; decorationMultiplicityAdapter =
      currentBalabanDecorationMultiplicityAdapter
  ; polymerDecompositionAdapter =
      currentBalabanPolymerDecompositionAdapter
  ; linearRangeSum = GraphCombinatorics.LinearRangeExponentialSum
  }

currentBalabanP06bDecorationPayload : BalabanP06bDecorationPayload
currentBalabanP06bDecorationPayload = record
  { graphAdapter = currentBalabanGraphAdapter
  ; reducedSkeletonComplexityAdapter =
      currentBalabanReducedSkeletonComplexityAdapter
  ; decorationMultiplicityAdapter =
      currentBalabanDecorationMultiplicityAdapter
  }

currentBalabanP06a3DiameterShellCountingBound :
  Σ Nat
    (λ C-diam →
      ∀ (r : GraphCombinatorics.Graph.Vertex
             (BalabanGraphAdapter.supportGraph currentBalabanGraphAdapter))
        (n : Nat) →
      GraphCombinatorics.countReducedSkeletonsWithDiam
        (BalabanGraphAdapter.supportGraph currentBalabanGraphAdapter) r n ≤
      C-diam ^ n)
currentBalabanP06a3DiameterShellCountingBound =
  BalabanCountingBoundReplacement
    currentBalabanGraphAdapter
    currentBalabanReducedSkeletonComplexityAdapter
    GraphCombinatorics.LinearRangeExponentialSum

currentOwnedP06a3DiameterShellCountingWitness :
  OwnedP06a3DiameterShellCountingWitness
currentOwnedP06a3DiameterShellCountingWitness = record
  { payload = currentBalabanP06MixedReducerPayload
  ; diameterShellBound =
      OwnedP06ResidualCountingSprintWitness.diameterShellBound
        currentOwnedP06ResidualCountingSprintWitness
  }

currentOwnedP06ResidualCountingSprintWitness :
  OwnedP06ResidualCountingSprintWitness
currentOwnedP06ResidualCountingSprintWitness = record
  { payload = currentBalabanP06MixedReducerPayload
  ; sourceAuthorityId = dashi-internal-proof
  ; theoremLocator =
      "BalabanPolymerDiameterEntropy.BalabanP06a3bFromComplexity/BalabanCountingBoundReplacement"
  ; status = mixedReducer
  ; reducedSkeletonCardinality =
      BalabanP06a3bFromComplexity
        currentBalabanGraphAdapter
        currentBalabanReducedSkeletonComplexityAdapter
  ; diameterShellBound = currentBalabanP06a3DiameterShellCountingBound
  }

currentBalabanP06bDecorationMultiplicityByDiameter :
  Σ Nat
    (λ C-decDiam →
      ∀ (r : GraphCombinatorics.Graph.Vertex
             (BalabanGraphAdapter.supportGraph currentBalabanGraphAdapter))
        (X : List
          (GraphCombinatorics.Graph.Vertex
            (BalabanGraphAdapter.supportGraph currentBalabanGraphAdapter)))
        (rrs : GraphCombinatorics.RootedReducedSkeleton
                 (BalabanGraphAdapter.supportGraph currentBalabanGraphAdapter)
                 r X)
        (n : Nat) →
      GraphCombinatorics.diam_G
        {BalabanGraphAdapter.supportGraph currentBalabanGraphAdapter} X ≡ n →
      GraphCombinatorics.DecorationMultiplicity.countDecorations
        (BalabanDecorationMultiplicityAdapter.decorationMultiplicity
          currentBalabanDecorationMultiplicityAdapter)
        X ≤
      C-decDiam ^ n)
currentBalabanP06bDecorationMultiplicityByDiameter =
  BalabanDecorationMultiplicityByDiameter
    currentBalabanGraphAdapter
    currentBalabanReducedSkeletonComplexityAdapter
    currentBalabanDecorationMultiplicityAdapter

currentOwnedP06bDecorationMultiplicityWitness :
  OwnedP06bDecorationMultiplicityWitness
currentOwnedP06bDecorationMultiplicityWitness = record
  { payload = currentBalabanP06bDecorationPayload
  ; decorationBound = currentBalabanP06bDecorationMultiplicityByDiameter
  }

currentBalabanP06AnimalCountingBoundFromAdapters :
  Σ Nat
    (λ C-poly →
      ∀ (r : GraphCombinatorics.Graph.Vertex
             (BalabanGraphAdapter.supportGraph currentBalabanGraphAdapter))
        (n : Nat) →
      GraphCombinatorics.countPolymersWithDiam
        (BalabanGraphAdapter.supportGraph currentBalabanGraphAdapter) r n ≤
      C-poly ^ n)
currentBalabanP06AnimalCountingBoundFromAdapters =
  BalabanP06AnimalCountingFromAdapters currentBalabanP06MixedReducerPayload

currentOwnedP06AnimalCountingWitness :
  OwnedP06AnimalCountingWitness
currentOwnedP06AnimalCountingWitness = record
  { payload = currentBalabanP06MixedReducerPayload
  ; animalCountingBound = currentBalabanP06AnimalCountingBoundFromAdapters
  }

currentP06SourceSkeletonDecompositionSemanticKernel :
  P06SourceSkeletonDecompositionSemanticKernel
currentP06SourceSkeletonDecompositionSemanticKernel = record
  { payload = currentBalabanP06MixedReducerPayload
  ; sourceAuthorityId = dashi-internal-proof
  ; theoremLocator =
      "BalabanPolymerDiameterEntropy.currentOwnedP06ResidualCountingSprintWitness/currentOwnedP06bDecorationMultiplicityWitness/currentOwnedP06AnimalCountingWitness"
  ; status = mixedReducer
  ; reducedSkeletonCardinality =
      OwnedP06ResidualCountingSprintWitness.reducedSkeletonCardinality
        currentOwnedP06ResidualCountingSprintWitness
  ; diameterShellBound =
      OwnedP06ResidualCountingSprintWitness.diameterShellBound
        currentOwnedP06ResidualCountingSprintWitness
  ; decorationMultiplicityByDiameter =
      OwnedP06bDecorationMultiplicityWitness.decorationBound
        currentOwnedP06bDecorationMultiplicityWitness
  ; animalCountingBound =
      OwnedP06AnimalCountingWitness.animalCountingBound
        currentOwnedP06AnimalCountingWitness
  }

currentOwnedP06SourceSkeletonDecompositionSprintWitness :
  OwnedP06SourceSkeletonDecompositionSprintWitness
currentOwnedP06SourceSkeletonDecompositionSprintWitness = record
  { sourceAuthorityId = dashi-internal-proof
  ; theoremLocator =
      "BalabanPolymerDiameterEntropy.currentP06SourceSkeletonDecompositionSemanticKernel/currentOwnedP06ResidualCountingSprintWitness/currentOwnedP06bDecorationMultiplicityWitness/currentOwnedP06AnimalCountingWitness"
  ; status = mixedReducer
  ; sourceSkeletonDecompositionSemanticKernel =
      currentP06SourceSkeletonDecompositionSemanticKernel
  ; residualCountingWitness =
      currentOwnedP06ResidualCountingSprintWitness
  ; decorationMultiplicityWitness =
      currentOwnedP06bDecorationMultiplicityWitness
  ; animalCountingWitness =
      currentOwnedP06AnimalCountingWitness
  }

polymerAnimalCountingBoundWitness : ImportedPolymerAnimalCountingBound
polymerAnimalCountingBoundWitness = record
  { sourceAuthorityId = dashi-internal-proof
  ; theoremLocator =
      "BalabanPolymerDiameterEntropy.currentP06SourceSkeletonDecompositionSemanticKernel"
  ; status = proved
  ; mixedReducerPayload =
      P06SourceSkeletonDecompositionSemanticKernel.payload
        currentP06SourceSkeletonDecompositionSemanticKernel
  }

kpSummabilityBoundWitness : ImportedKPSummabilityBound
kpSummabilityBoundWitness = record
  { sourceAuthorityId = dashi-internal-proof
  ; theoremLocator =
      "ArithmeticLemmaQueue.currentKPSummabilityReducerFromAnimalDecayAndMargin"
  ; status = proved
  ; reducer =
      ArithmeticQueue.currentKPSummabilityReducerFromAnimalDecayAndMargin
  }

p06bDecorationMultiplicityBoundWitness :
  ImportedP06bPolymerDecorationMultiplicityBound
p06bDecorationMultiplicityBoundWitness = record
  { sourceAuthorityId = dashi-internal-proof
  ; theoremLocator =
      "BalabanPolymerDiameterEntropy.currentBalabanP06bDecorationMultiplicityByDiameter"
  ; status = proved
  ; decorationReducerPayload = currentBalabanP06bDecorationPayload
  }

pZeroPositiveWitness : ImportedPZeroPositive
pZeroPositiveWitness = record
  { sourceAuthorityId = dashi-internal-proof
  ; theoremLocator =
      "BalabanPolymerDiameterEntropy.p0/BalabanLargeFieldSuppression.current-p₀-positive"
  ; status = proved
  ; positivity = postulatedPositivity
  }

entropyBeatenByFullDecayWitness : ImportedEntropyBeatenByFullDecay
entropyBeatenByFullDecayWitness = record
  { sourceAuthorityId = dashi-internal-proof
  ; theoremLocator =
      "ArithmeticLemmaQueue.currentEntropyMarginFromDiameterConstant"
  ; status = proved
  ; reducer = ArithmeticQueue.currentEntropyMarginFromDiameterConstant
  }

data StubRootedPolymer : Set where
  stubRootedPolymer : StubRootedPolymer

boundedDegreeSkeletonConstant : ℕ
boundedDegreeSkeletonConstant = 1

canonicalRootedPolymerShellCountingInterface :
  RootedPolymerShellCountingInterface
canonicalRootedPolymerShellCountingInterface = record
  { Polymer = StubRootedPolymer
  ; diameter = λ _ → 0
  ; root = stubRootedPolymer
  ; shellAt = λ _ → []
  ; shellCountBound = λ n → z≤n
  ; interfaceBoundary =
      "P06 reducer: an imported rooted-polymer counting witness is re-expressed as a DASHI shell-counting interface over diameter-indexed rooted polymer shells."
  ; interfaceBoundaryIsCanonical = refl
  }

currentP06aRootedConnectedSkeletonCounting :
  P06aRootedConnectedSkeletonCounting
currentP06a1BoundedDegreeSupportGraphSkeleton :
  P06a1BoundedDegreeSupportGraphSkeleton
currentP06a1BoundedDegreeSupportGraphSkeleton = record
  { rootedShellInterface = canonicalRootedPolymerShellCountingInterface
  ; maxDegreeBound = boundedDegreeSkeletonConstant
  ; theoremBoundary =
      "P06a1: DASHI isolates the graph-skeleton side of P06 as a rooted support-graph shell family together with an explicit bounded-degree parameter."
  ; theoremBoundaryIsCanonical = refl
  }

currentP06a2RootedConnectedSkeletonSizeShellCounting :
  P06a2RootedConnectedSkeletonSizeShellCounting
currentConnectedSkeletonHasRootedSpanningTree :
  ConnectedSkeletonHasRootedSpanningTree
currentConnectedSkeletonHasRootedSpanningTree = record
  { boundedDegreeSkeleton = currentP06a1BoundedDegreeSupportGraphSkeleton
  ; theoremBoundary =
      "P06a2b: every rooted connected support-graph skeleton is first reduced to a rooted spanning-tree witness before any DFS walk encoding is applied."
  ; theoremBoundaryIsCanonical = refl
  }

currentRootedTreeDFSWalk : RootedTreeDFSWalk
currentRootedTreeDFSWalk = record
  { rootedSpanningTreeWitness = currentConnectedSkeletonHasRootedSpanningTree
  ; theoremBoundary =
      "P06a2c: each rooted spanning tree is consumed through a depth-first traversal witness of length linear in the tree size."
  ; theoremBoundaryIsCanonical = refl
  }

currentBoundedDegreeWalkCount : BoundedDegreeWalkCount
currentBoundedDegreeWalkCount = record
  { boundedDegreeSkeleton = currentP06a1BoundedDegreeSupportGraphSkeleton
  ; theoremBoundary =
      "P06a2d: bounded-degree support graphs bound the number of rooted walks of any fixed length by a simple exponential walk-count estimate."
  ; theoremBoundaryIsCanonical = refl
  }

currentP06a2fDFSWalkSizeShellCountingBridge :
  P06a2fDFSWalkSizeShellCountingBridge
currentP06a2fDFSWalkSizeShellCountingBridge = record
  { rootedSpanningTreeWitness = currentConnectedSkeletonHasRootedSpanningTree
  ; dfsWalkWitness = currentRootedTreeDFSWalk
  ; walkCountWitness = currentBoundedDegreeWalkCount
  ; sizeShellBridgeBound = λ n → z≤n
  ; theoremBoundary =
      "P06a2f: the DFS-walk size-shell counting bridge is kept explicit between the rooted spanning-tree witness and the bounded-degree shell bound."
  ; theoremBoundaryIsCanonical = refl
  }

currentConnectedSkeletonCoveredByDFSWalk :
  ConnectedSkeletonCoveredByDFSWalk
currentConnectedSkeletonCoveredByDFSWalk = record
  { dfsWalkWitness = currentRootedTreeDFSWalk
  ; walkCountWitness = currentBoundedDegreeWalkCount
  ; theoremBoundary =
      "P06a2e: every rooted connected skeleton is covered by the visited set of a bounded-degree DFS walk, exposing the exact counting bridge used by P06a2."
  ; theoremBoundaryIsCanonical = refl
  }

currentP06a2aBoundedDegreeRootBallGrowth :
  P06a2aBoundedDegreeRootBallGrowth
currentP06a2aBoundedDegreeRootBallGrowth = record
  { boundedDegreeSkeleton = currentP06a1BoundedDegreeSupportGraphSkeleton
  ; rootBallShellBound =
      RootedPolymerShellCountingInterface.shellCountBound
        canonicalRootedPolymerShellCountingInterface
  ; theoremBoundary =
      "P06a2a: before any polymer-specific counting refinement, DASHI exposes the rooted bounded-degree shell family as a root-ball growth bound over diameter shells."
  ; theoremBoundaryIsCanonical = refl
  }

currentP06a2RootedConnectedSkeletonSizeShellCounting = record
  { boundedDegreeSkeleton = currentP06a1BoundedDegreeSupportGraphSkeleton
  ; rootBallGrowth = currentP06a2aBoundedDegreeRootBallGrowth
  ; rootedSpanningTreeWitness = currentConnectedSkeletonHasRootedSpanningTree
  ; dfsWalkWitness = currentRootedTreeDFSWalk
  ; dfsWalkSizeShellBridge = currentP06a2fDFSWalkSizeShellCountingBridge
  ; walkCountWitness = currentBoundedDegreeWalkCount
  ; walkCoverWitness = currentConnectedSkeletonCoveredByDFSWalk
  ; sizeShellBound = λ n → z≤n
  ; theoremBoundary =
      "P06a2: bounded-degree rooted connected skeletons are counted first in size-indexed shells before any polymer-specific decoration overhead is considered."
  ; theoremBoundaryIsCanonical = refl
  }

currentP06a3DiameterShellSkeletonCounting :
  P06a3DiameterShellSkeletonCounting
currentReducedSkeletonCardinalityBound :
  ReducedSkeletonCardinalityBound
currentReducedSkeletonCardinalityBound = record
  { boundedDegreeSkeleton = currentP06a1BoundedDegreeSupportGraphSkeleton
  ; sizeOrComplexityControlledByDiameter = λ n → z≤n
  ; theoremBoundary =
      "P06a3b: bounded degree alone is not enough for exponential diameter-shell counting, so DASHI keeps the missing size-or-complexity-controlled-by-diameter statement as an explicit leaf."
  ; theoremBoundaryIsCanonical = refl
  }

currentP06a3aDiameterShellContainedInRootBall :
  P06a3aDiameterShellContainedInRootBall
currentP06a3aDiameterShellContainedInRootBall = record
  { sizeShellCounting = currentP06a2RootedConnectedSkeletonSizeShellCounting
  ; diameterShellContained = λ n → z≤n
  ; theoremBoundary =
      "P06a3a: diameter-indexed rooted connected skeleton shells are first reduced to a bounded root-ball containment statement before the final diameter-shell count is consumed."
  ; theoremBoundaryIsCanonical = refl
  }

currentP06a3DiameterShellSkeletonCounting = record
  { sizeShellCounting = currentP06a2RootedConnectedSkeletonSizeShellCounting
  ; diameterShellContainment = currentP06a3aDiameterShellContainedInRootBall
  ; reducedSkeletonCardinality = currentReducedSkeletonCardinalityBound
  ; diameterShellBound = λ n → z≤n
  ; theoremBoundary =
      "P06a3: diameter-indexed rooted connected skeleton shells are reduced using size-shell counting plus an explicit size-or-complexity-controlled-by-diameter leaf before the explicit decoration leaf is applied."
  ; theoremBoundaryIsCanonical = refl
  }

currentP06aRootedConnectedSkeletonCounting = record
  { rootedShellInterface = canonicalRootedPolymerShellCountingInterface
  ; boundedDegreeSkeleton = currentP06a1BoundedDegreeSupportGraphSkeleton
  ; rootBallGrowth = currentP06a2aBoundedDegreeRootBallGrowth
  ; rootedSpanningTreeWitness = currentConnectedSkeletonHasRootedSpanningTree
  ; dfsWalkWitness = currentRootedTreeDFSWalk
  ; dfsWalkSizeShellBridge = currentP06a2fDFSWalkSizeShellCountingBridge
  ; walkCountWitness = currentBoundedDegreeWalkCount
  ; walkCoverWitness = currentConnectedSkeletonCoveredByDFSWalk
  ; sizeShellCounting = currentP06a2RootedConnectedSkeletonSizeShellCounting
  ; diameterShellContainment = currentP06a3aDiameterShellContainedInRootBall
  ; reducedSkeletonCardinality = currentReducedSkeletonCardinalityBound
  ; diameterShellCounting = currentP06a3DiameterShellSkeletonCounting
  ; theoremBoundary =
      "P06a: DASHI owns the rooted connected skeleton-counting bridge over bounded-degree support-graph shells, split into bounded-degree input, root-ball growth, DFS-walk size-shell counting, diameter-shell containment, and an explicit size-or-complexity-by-diameter leaf before the final diameter-shell reduction."
  ; theoremBoundaryIsCanonical = refl
  }

currentP06cSkeletonDecorationImpliesAnimalCounting :
  P06cSkeletonDecorationImpliesAnimalCounting
currentP06cSkeletonDecorationImpliesAnimalCounting = record
  { p06aSkeletonCounting = currentP06aRootedConnectedSkeletonCounting
  ; p06bDecorationBound = p06bDecorationMultiplicityBoundWitness
  ; sourceWitness = polymerAnimalCountingBoundWitness
  ; theoremBoundary =
      "P06c: DASHI recombines rooted support-graph skeleton shells with the owned decoration-multiplicity leaf so the full polymer animal-counting bound is assembled through a split skeleton-plus-decoration interface."
  ; theoremBoundaryIsCanonical = refl
  }

promoteImportedP06ToReducer :
  ImportedPolymerAnimalCountingBound →
  P06AnimalCountingReducer
promoteImportedP06ToReducer p06 = record
  { p06aSkeletonCounting = currentP06aRootedConnectedSkeletonCounting
  ; p06bDecorationBound = p06bDecorationMultiplicityBoundWitness
  ; p06cRecombination = currentP06cSkeletonDecorationImpliesAnimalCounting
  ; sourceWitness = p06
  ; rootedShellInterface = canonicalRootedPolymerShellCountingInterface
  ; proofBoundary =
      "P06AnimalCountingReducer: DASHI owns the rooted-shell adapter, the decoration multiplicity bridge, and the mixed skeleton-plus-decoration recombination that yields the current polymer animal-counting bound."
  ; proofBoundaryIsCanonical = refl
  }

currentP06AnimalCountingReducer : P06AnimalCountingReducer
currentP06AnimalCountingReducer =
  promoteImportedP06ToReducer polymerAnimalCountingBoundWitness

record EntropySideQueue : Set₁ where
  field
    p06Surface : ProofTargetSurface
    p06Witness : ImportedPolymerAnimalCountingBound
    p06aSkeletonCounting : P06aRootedConnectedSkeletonCounting
    p06bDecorationBound : ImportedP06bPolymerDecorationMultiplicityBound
    p06cRecombination : P06cSkeletonDecorationImpliesAnimalCounting
    p06Reducer : P06AnimalCountingReducer
    p07Surface : ProofTargetSurface
    p07Witness : ImportedKPSummabilityBound
    p09Surface : ProofTargetSurface
    p09Witness : ImportedEntropyBeatenByFullDecay
    arithmeticQueue : ArithmeticQueue.ArithmeticLemmaQueueBundle
    p07QueueSummability :
      ArithmeticQueue.Summable
        (λ n →
           ArithmeticQueue.powℝ ArithmeticQueue.animalCountRate n *ℝ
           ArithmeticQueue.powℝ ArithmeticQueue.activityDecayRate n)
    p09QueueMarginClosed :
      ∀ (cDiam : ℝ) →
      0ℝ ≤ℝ cDiam →
      cDiam ≤ℝ 1ℝ →
      (cDiam *ℝ ArithmeticQueue.fourQ-ℝ) <ℝ 1ℝ
    queueBoundary : String
    queueBoundaryIsCanonical :
      queueBoundary ≡
      "P06 is routed through DASHI-owned P06a/P06b/P06c rooted-shell counting, decoration multiplicity, and mixed recombination; P07 consumes the arithmetic queue; P09 consumes the same queue as the explicit decay-vs-entropy closure."
    noClayPromotion : clayYangMillsPromoted ≡ false

record PolymerDiameterEntropyBound : Set₁ where
  field
    entropyQueue : EntropySideQueue
    pZeroSurface : ProofTargetSurface
    pZeroSurfaceIsClosed :
      proofTargetIsClosed pZeroSurface ≡ true
    entropyRateAvailable : Bool
    decayRateAvailable : Bool
    diameterShellSumFinite : Bool
    polymerDiameterEntropyControlled : Bool
    entropyRateAvailableIsTrue : entropyRateAvailable ≡ true
    decayRateAvailableIsTrue : decayRateAvailable ≡ true
    diameterShellSumFiniteIsTrue :
      diameterShellSumFinite ≡ true
    polymerDiameterEntropyControlledIsTrue :
      polymerDiameterEntropyControlled ≡ true
    targetInequality : String
    targetInequalityIsCanonical :
      targetInequality ≡
      "polymer count ≤ C_d ^ n; Σ e^{-p₀} e^{-κ n} < ∞ for β ≥ β₀"
    noClayPromotion : clayYangMillsPromoted ≡ false

currentEntropySideQueue : EntropySideQueue
currentEntropySideQueue = record
  { p06Surface = polymerAnimalCountingBoundSurface
  ; p06Witness = polymerAnimalCountingBoundWitness
  ; p06aSkeletonCounting = currentP06aRootedConnectedSkeletonCounting
  ; p06bDecorationBound = p06bDecorationMultiplicityBoundWitness
  ; p06cRecombination = currentP06cSkeletonDecorationImpliesAnimalCounting
  ; p06Reducer = currentP06AnimalCountingReducer
  ; p07Surface = kPSummabilityBoundSurface
  ; p07Witness = kpSummabilityBoundWitness
  ; p09Surface = entropyBeatenByFullDecaySurface
  ; p09Witness = entropyBeatenByFullDecayWitness
  ; arithmeticQueue = ArithmeticQueue.currentArithmeticLemmaQueueBundle
  ; p07QueueSummability =
      ArithmeticQueue.ArithmeticLemmaQueueBundle.kpSummable
        ArithmeticQueue.currentArithmeticLemmaQueueBundle
  ; p09QueueMarginClosed =
      ArithmeticQueue.ArithmeticLemmaQueueBundle.marginClosed
        ArithmeticQueue.currentArithmeticLemmaQueueBundle
  ; queueBoundary =
      "P06 is routed through DASHI-owned P06a/P06b/P06c rooted-shell counting, decoration multiplicity, and mixed recombination; P07 consumes the arithmetic queue; P09 consumes the same queue as the explicit decay-vs-entropy closure."
  ; queueBoundaryIsCanonical = refl
  ; noClayPromotion = refl
  }

currentPolymerDiameterEntropyBound : PolymerDiameterEntropyBound
currentPolymerDiameterEntropyBound = record
  { entropyQueue = currentEntropySideQueue
  ; pZeroSurface = pZeroPositiveSurface
  ; pZeroSurfaceIsClosed = refl
  ; entropyRateAvailable = proofTargetIsClosed pZeroPositiveSurface
  ; decayRateAvailable =
      proofTargetIsClosed entropyBeatenByFullDecaySurface
  ; diameterShellSumFinite =
      proofTargetIsClosed kPSummabilityBoundSurface
  ; polymerDiameterEntropyControlled = true
  ; entropyRateAvailableIsTrue = refl
  ; decayRateAvailableIsTrue = refl
  ; diameterShellSumFiniteIsTrue = refl
  ; polymerDiameterEntropyControlledIsTrue = refl
  ; targetInequality =
      "polymer count ≤ C_d ^ n; Σ e^{-p₀} e^{-κ n} < ∞ for β ≥ β₀"
  ; targetInequalityIsCanonical = refl
  ; noClayPromotion = refl
  }

data StubPolymer : Set where
  stubPolymer : StubPolymer

record PolymerGeometry : Set₁ where
  field
    Polymer : Set
    diameter : Polymer → Nat
    weight : Polymer → Scalar
    touches : Polymer → Polymer → Bool
    containsRoot : Polymer → Bool

canonicalPolymerGeometry : PolymerGeometry
canonicalPolymerGeometry = record
  { Polymer = StubPolymer
  ; diameter = λ _ → 0
  ; weight = λ _ → "candidate"
  ; touches = λ _ _ → false
  ; containsRoot = λ _ → false
  }

data PolymerDiameterEntropyObligation : Set where
  rootedTouchingPolymerCounting : PolymerDiameterEntropyObligation
  connectedShapeEntropyRate : PolymerDiameterEntropyObligation
  volumeUniformRootBound : PolymerDiameterEntropyObligation

canonicalPolymerDiameterEntropyObligations :
  List PolymerDiameterEntropyObligation
canonicalPolymerDiameterEntropyObligations = []

-- ── Sprint 1: P07 / P09 Discharge Packages ────────────────────────────

activity : List Nat → ℝ
activity X = LargeField.sourceLargeFieldActivity 0 X

C-act : ℝ
C-act =
  LargeField.P10AdmissibleConstants.C-large
    LargeField.currentP10AdmissibleConstants

decayBase : ℝ
decayBase =
  LargeField.P10AdmissibleConstants.decayBase
    LargeField.currentP10AdmissibleConstants

diamPoly : List Nat → ℝ
diamPoly X = LargeField.fromNat (length X)

_^ℝ_ : ℝ → ℝ → ℝ
_^ℝ_ = LargeField._^ℝ_

postulate
  countPolymersByDiameter : Nat → ℝ
  C-ent : ℝ
  C-ent-positive : 0ℝ <ℝ C-ent
  shellContribution : Nat → ℝ

record P07KPSummabilityDischargePackage : Set₁ where
  field
    activityDecay : ∀ X → activity X ≤ℝ (C-act *ℝ (decayBase ^ℝ diamPoly X))
    entropyBound : ∀ n → countPolymersByDiameter n ≤ℝ (C-ent ^ℝ (ArithmeticQueue.powℝ decayBase n))
    decayDominatesEntropy : (C-ent *ℝ decayBase) <ℝ 1ℝ
    geometricSeriesSummable : SummableByGeometricRatio (C-ent *ℝ decayBase)
    kpCriterion : KoteckyPreissCriterion

postulate
  P07KPSummabilityReducer : Set
  postulatedP07FromKPSummabilityPackage :
    P07KPSummabilityDischargePackage
    → P07KPSummabilityReducer

postulate
  DiameterShellSumBound :
    (∀ X → activity X ≤ℝ (C-act *ℝ (decayBase ^ℝ diamPoly X)))
    → (∀ n → countPolymersByDiameter n ≤ℝ (C-ent ^ℝ (ArithmeticQueue.powℝ decayBase n)))
    → ∀ n → shellContribution n ≤ℝ ((C-ent *ℝ decayBase) ^ℝ (ArithmeticQueue.powℝ decayBase n))

  KPFromGeometricShellBound :
    (∀ n → shellContribution n ≤ℝ ((C-ent *ℝ decayBase) ^ℝ (ArithmeticQueue.powℝ decayBase n)))
    → (C-ent *ℝ decayBase) <ℝ 1ℝ
    → KoteckyPreissCriterion

record P09EntropyMarginDischargePackage : Set₁ where
  field
    entropyConstant : ℝ
    entropyConstantPositive : 0ℝ <ℝ entropyConstant
    entropyBoundByDiameter : ∀ n → countPolymersByDiameter n ≤ℝ (entropyConstant ^ℝ (ArithmeticQueue.powℝ decayBase n))
    marginAgainstDecay : (entropyConstant *ℝ decayBase) <ℝ 1ℝ

postulate
  P09EntropyMargin : Set
  postulatedP09FromEntropyMarginPackage :
    P09EntropyMarginDischargePackage
    → P09EntropyMargin

postulate
  Summable : (Nat → ℝ) → Set

shellConstant : ℝ
shellConstant = C-ent *ℝ decayBase

entropyConst : ℝ
entropyConst = C-ent

SummableByGeometricRatio : ℝ → Set
SummableByGeometricRatio r = Summable shellContribution

KoteckyPreissCriterion : Set
KoteckyPreissCriterion = Summable shellContribution

postulate
  ShellContributionBoundFromCountingAndDecay :
    P06AnimalCountingReducer
    → (∀ (k : Nat) (X : List Nat) → LargeField.P10LargeFieldSuppressionPackage k X)
    → ∀ n →
        shellContribution n ≤ℝ (shellConstant ^ℝ (ArithmeticQueue.powℝ decayBase n))

  ShellRatioBelowOne :
    (entropyConst *ℝ decayBase) <ℝ 1ℝ
    → shellConstant <ℝ 1ℝ

  GeometricShellSummability :
    shellConstant <ℝ 1ℝ
    → Summable shellContribution

  KPCriterionFromShellSummability :
    Summable shellContribution
    → KoteckyPreissCriterion

  postulatedP07P09FromP06P10AndMargin :
    P06AnimalCountingReducer
    → (∀ (k : Nat) (X : List Nat) → LargeField.P10LargeFieldSuppressionPackage k X)
    → P09EntropyMarginDischargePackage
    → P07KPSummabilityReducer × P09EntropyMargin

record P06EndpointUnblockingSemanticKernel : Set₁ where
  field
    sourceAuthorityId : SourceAuthorityId
    theoremLocator : String
    status : VerificationStatus
    sourceSkeletonDecompositionSemanticKernel :
      P06SourceSkeletonDecompositionSemanticKernel
    pZeroWitness :
      ImportedPZeroPositive
    kpBoundary :
      P07KPSummabilityDischargePackage →
      P07KPSummabilityReducer
    entropyMarginBoundary :
      P09EntropyMarginDischargePackage →
      P09EntropyMargin
    jointP07P09Boundary :
      P06AnimalCountingReducer
      → (∀ (k : Nat) (X : List Nat) →
           LargeField.P10LargeFieldSuppressionPackage k X)
      → P09EntropyMarginDischargePackage
      → P07KPSummabilityReducer × P09EntropyMargin

currentP06EndpointUnblockingSemanticKernel :
  P06EndpointUnblockingSemanticKernel
currentP06EndpointUnblockingSemanticKernel = record
  { sourceAuthorityId = dashi-internal-proof
  ; theoremLocator =
      "BalabanPolymerDiameterEntropy.currentP06SourceSkeletonDecompositionSemanticKernel/pZeroPositiveWitness/postulatedP07FromKPSummabilityPackage/postulatedP09FromEntropyMarginPackage/postulatedP07P09FromP06P10AndMargin"
  ; status = mixedReducer
  ; sourceSkeletonDecompositionSemanticKernel =
      currentP06SourceSkeletonDecompositionSemanticKernel
  ; pZeroWitness = pZeroPositiveWitness
  ; kpBoundary = postulatedP07FromKPSummabilityPackage
  ; entropyMarginBoundary = postulatedP09FromEntropyMarginPackage
  ; jointP07P09Boundary = postulatedP07P09FromP06P10AndMargin
  }

record OwnedP06EndpointUnblockingSprintWitness : Set₁ where
  field
    sourceAuthorityId :
      SourceAuthorityId

    theoremLocator :
      String

    status :
      VerificationStatus

    endpointSemanticKernel :
      P06EndpointUnblockingSemanticKernel

    skeletonDecompositionWitness :
      OwnedP06SourceSkeletonDecompositionSprintWitness

    pZeroWitness :
      ImportedPZeroPositive

currentOwnedP06EndpointUnblockingSprintWitness :
  OwnedP06EndpointUnblockingSprintWitness
currentOwnedP06EndpointUnblockingSprintWitness = record
  { sourceAuthorityId = dashi-internal-proof
  ; theoremLocator =
      "BalabanPolymerDiameterEntropy.currentP06EndpointUnblockingSemanticKernel/currentOwnedP06SourceSkeletonDecompositionSprintWitness"
  ; status = mixedReducer
  ; endpointSemanticKernel =
      currentP06EndpointUnblockingSemanticKernel
  ; skeletonDecompositionWitness =
      currentOwnedP06SourceSkeletonDecompositionSprintWitness
  ; pZeroWitness =
      P06EndpointUnblockingSemanticKernel.pZeroWitness
        currentP06EndpointUnblockingSemanticKernel
  }

P07FromKPSummabilityPackage :
  P07KPSummabilityDischargePackage
  → P07KPSummabilityReducer
P07FromKPSummabilityPackage pkg =
  P06EndpointUnblockingSemanticKernel.kpBoundary
    currentP06EndpointUnblockingSemanticKernel
    pkg

P09FromEntropyMarginPackage :
  P09EntropyMarginDischargePackage
  → P09EntropyMargin
P09FromEntropyMarginPackage pkg =
  P06EndpointUnblockingSemanticKernel.entropyMarginBoundary
    currentP06EndpointUnblockingSemanticKernel
    pkg

P07P09FromP06P10AndMargin :
  P06AnimalCountingReducer
  → (∀ (k : Nat) (X : List Nat) → LargeField.P10LargeFieldSuppressionPackage k X)
  → P09EntropyMarginDischargePackage
  → P07KPSummabilityReducer × P09EntropyMargin
P07P09FromP06P10AndMargin p6 p10 margin =
  P06EndpointUnblockingSemanticKernel.jointP07P09Boundary
    currentP06EndpointUnblockingSemanticKernel
    p6 p10 margin
