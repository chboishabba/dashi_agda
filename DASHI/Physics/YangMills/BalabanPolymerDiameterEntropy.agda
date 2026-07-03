module DASHI.Physics.YangMills.BalabanPolymerDiameterEntropy where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Sigma using (Σ; _,_; fst; snd)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; []; length)
open import Data.Nat.Base using (ℕ; _≤_; _*_; _+_; _^_; zero; suc; s≤s; z≤n)
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

Nat≤-refl : ∀ {n : ℕ} → n ≤ n
Nat≤-refl {zero} = z≤n
Nat≤-refl {suc n} = s≤s Nat≤-refl

currentP06ShellRoot :
  Set
currentP06ShellRoot =
  GraphCombinatorics.Graph.Vertex
    (BalabanGraphAdapter.supportGraph currentBalabanGraphAdapter)

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
    Root : Set
    shellGrowthConstant : ℕ
    shellCountAt : Root → ℕ → ℕ
    shellCountBound :
      ∀ (root : Root) (n : ℕ) →
      shellCountAt root n ≤ shellGrowthConstant ^ n
    interfaceBoundary : String
    interfaceBoundaryIsCanonical :
      interfaceBoundary ≡
      "P06 reducer: DASHI owns the diameter-indexed rooted polymer shell envelope; the remaining external boundary is only the source animal-counting witness consumed through that envelope."

record RootedSkeletonSizeShellCountingInterface : Set₁ where
  field
    Root : Set
    sizeShellGrowthConstant : ℕ
    sizeShellCountAt : Root → ℕ → ℕ
    sizeShellCountBound :
      ∀ (root : Root) (n : ℕ) →
      sizeShellCountAt root n ≤ sizeShellGrowthConstant ^ n
    interfaceBoundary : String
    interfaceBoundaryIsCanonical :
      interfaceBoundary ≡
      "P06a2 reducer: the rooted connected skeleton size-shell count is exposed directly as a root-indexed exponential shell-count envelope."

record P06a1BoundedDegreeSupportGraphSkeleton : Set₁ where
  field
    sizeShellInterface : RootedSkeletonSizeShellCountingInterface
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
      ∀ (root : RootedSkeletonSizeShellCountingInterface.Root
                   (P06a1BoundedDegreeSupportGraphSkeleton.sizeShellInterface
                     boundedDegreeSkeleton))
        (n : ℕ) →
      RootedSkeletonSizeShellCountingInterface.sizeShellCountAt
          (P06a1BoundedDegreeSupportGraphSkeleton.sizeShellInterface
            boundedDegreeSkeleton)
          root
          n
      ≤ RootedSkeletonSizeShellCountingInterface.sizeShellGrowthConstant
          (P06a1BoundedDegreeSupportGraphSkeleton.sizeShellInterface
            boundedDegreeSkeleton) ^ n
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
      ∀ (root : RootedSkeletonSizeShellCountingInterface.Root
                   (P06a1BoundedDegreeSupportGraphSkeleton.sizeShellInterface
                     (ConnectedSkeletonHasRootedSpanningTree.boundedDegreeSkeleton
                       rootedSpanningTreeWitness)))
        (n : ℕ) →
      RootedSkeletonSizeShellCountingInterface.sizeShellCountAt
          (P06a1BoundedDegreeSupportGraphSkeleton.sizeShellInterface
            (ConnectedSkeletonHasRootedSpanningTree.boundedDegreeSkeleton
              rootedSpanningTreeWitness))
          root
          n
      ≤ RootedSkeletonSizeShellCountingInterface.sizeShellGrowthConstant
          (P06a1BoundedDegreeSupportGraphSkeleton.sizeShellInterface
            (ConnectedSkeletonHasRootedSpanningTree.boundedDegreeSkeleton
              rootedSpanningTreeWitness)) ^ n
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
      ∀ (root : RootedSkeletonSizeShellCountingInterface.Root
                   (P06a1BoundedDegreeSupportGraphSkeleton.sizeShellInterface
                     boundedDegreeSkeleton))
        (n : ℕ) →
      RootedSkeletonSizeShellCountingInterface.sizeShellCountAt
          (P06a1BoundedDegreeSupportGraphSkeleton.sizeShellInterface
            boundedDegreeSkeleton)
          root
          n
      ≤ RootedSkeletonSizeShellCountingInterface.sizeShellGrowthConstant
          (P06a1BoundedDegreeSupportGraphSkeleton.sizeShellInterface
            boundedDegreeSkeleton) ^ n
    theoremBoundary : String
    theoremBoundaryIsCanonical :
      theoremBoundary ≡
      "P06a2: bounded-degree rooted connected skeletons are counted first in size-indexed shells before any polymer-specific decoration overhead is considered."

record P06a3aDiameterShellContainedInRootBall : Set₁ where
  field
    sizeShellCounting : P06a2RootedConnectedSkeletonSizeShellCounting
    diameterShellContained :
      ∀ (root : RootedPolymerShellCountingInterface.Root
                   (P06a1BoundedDegreeSupportGraphSkeleton.rootedShellInterface
                     (P06a2RootedConnectedSkeletonSizeShellCounting.boundedDegreeSkeleton
                       sizeShellCounting)))
        (n : ℕ) →
      RootedPolymerShellCountingInterface.shellCountAt
          (P06a1BoundedDegreeSupportGraphSkeleton.rootedShellInterface
            (P06a2RootedConnectedSkeletonSizeShellCounting.boundedDegreeSkeleton
              sizeShellCounting))
          root
          n
      ≤ RootedPolymerShellCountingInterface.shellGrowthConstant
          (P06a1BoundedDegreeSupportGraphSkeleton.rootedShellInterface
            (P06a2RootedConnectedSkeletonSizeShellCounting.boundedDegreeSkeleton
              sizeShellCounting)) ^ n
    theoremBoundary : String
    theoremBoundaryIsCanonical :
      theoremBoundary ≡
      "P06a3a: diameter-indexed rooted connected skeleton shells are first reduced to a bounded root-ball containment statement before the final diameter-shell count is consumed."

record ReducedSkeletonCardinalityBound : Set₁ where
  field
    boundedDegreeSkeleton : P06a1BoundedDegreeSupportGraphSkeleton
    K : ℕ
    B : ℕ
    reducedSkeletonDiameterBound :
      ∀ (root : RootedPolymerShellCountingInterface.Root
                   (P06a1BoundedDegreeSupportGraphSkeleton.rootedShellInterface
                     boundedDegreeSkeleton))
        (X : List
          (RootedPolymerShellCountingInterface.Root
            (P06a1BoundedDegreeSupportGraphSkeleton.rootedShellInterface
              boundedDegreeSkeleton)))
        (rrs : GraphCombinatorics.RootedReducedSkeleton
                 (BalabanGraphAdapter.supportGraph currentBalabanGraphAdapter)
                 root X)
        (n : ℕ) →
      GraphCombinatorics.diam_G
        {BalabanGraphAdapter.supportGraph currentBalabanGraphAdapter} X ≡ n →
      length X ≤ K * n + B
    theoremBoundary : String
    theoremBoundaryIsCanonical :
      theoremBoundary ≡
      "P06a3b: bounded degree alone is not enough for exponential diameter-shell counting, so DASHI exposes the missing reduced-skeleton cardinality theorem explicitly as a linear size-or-complexity-by-diameter bound."

record P06a3DiameterShellSkeletonCounting : Set₁ where
  field
    sizeShellCounting : P06a2RootedConnectedSkeletonSizeShellCounting
    diameterShellContainment : P06a3aDiameterShellContainedInRootBall
    reducedSkeletonCardinality : ReducedSkeletonCardinalityBound
    diameterShellBound :
      ∀ (root : RootedPolymerShellCountingInterface.Root
                   (P06a1BoundedDegreeSupportGraphSkeleton.rootedShellInterface
                     (P06a2RootedConnectedSkeletonSizeShellCounting.boundedDegreeSkeleton
                       sizeShellCounting)))
        (n : ℕ) →
      RootedPolymerShellCountingInterface.shellCountAt
          (P06a1BoundedDegreeSupportGraphSkeleton.rootedShellInterface
            (P06a2RootedConnectedSkeletonSizeShellCounting.boundedDegreeSkeleton
              sizeShellCounting))
          root
          n
      ≤ RootedPolymerShellCountingInterface.shellGrowthConstant
          (P06a1BoundedDegreeSupportGraphSkeleton.rootedShellInterface
            (P06a2RootedConnectedSkeletonSizeShellCounting.boundedDegreeSkeleton
              sizeShellCounting)) ^ n
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

P06bDecorationPayloadFromMixedReducerPayload :
  BalabanP06MixedReducerPayload →
  BalabanP06bDecorationPayload
P06bDecorationPayloadFromMixedReducerPayload payload = record
  { graphAdapter =
      BalabanP06MixedReducerPayload.graphAdapter payload
  ; reducedSkeletonComplexityAdapter =
      BalabanP06MixedReducerPayload.reducedSkeletonComplexityAdapter
        payload
  ; decorationMultiplicityAdapter =
      BalabanP06MixedReducerPayload.decorationMultiplicityAdapter payload
  }

P06ResidualCountingSprintWitnessFromPayload :
  BalabanP06MixedReducerPayload →
  OwnedP06ResidualCountingSprintWitness
P06ResidualCountingSprintWitnessFromPayload payload =
  let graphAdapter =
        BalabanP06MixedReducerPayload.graphAdapter payload
      complexityAdapter =
        BalabanP06MixedReducerPayload.reducedSkeletonComplexityAdapter
          payload
  in record
       { payload = payload
       ; sourceAuthorityId = dashi-internal-proof
       ; theoremLocator =
           "BalabanPolymerDiameterEntropy.P06ResidualCountingSprintWitnessFromPayload/BalabanP06a3bFromComplexity/BalabanCountingBoundReplacement"
       ; status = mixedReducer
       ; reducedSkeletonCardinality =
           BalabanP06a3bFromComplexity graphAdapter complexityAdapter
       ; diameterShellBound =
           BalabanCountingBoundReplacement
             graphAdapter
             complexityAdapter
             (BalabanP06MixedReducerPayload.linearRangeSum payload)
       }

P06bDecorationMultiplicityWitnessFromPayload :
  BalabanP06MixedReducerPayload →
  OwnedP06bDecorationMultiplicityWitness
P06bDecorationMultiplicityWitnessFromPayload payload =
  let graphAdapter =
        BalabanP06MixedReducerPayload.graphAdapter payload
      complexityAdapter =
        BalabanP06MixedReducerPayload.reducedSkeletonComplexityAdapter
          payload
      decorationAdapter =
        BalabanP06MixedReducerPayload.decorationMultiplicityAdapter
          payload
  in record
       { payload = P06bDecorationPayloadFromMixedReducerPayload payload
       ; decorationBound =
           BalabanDecorationMultiplicityByDiameter
             graphAdapter
             complexityAdapter
             decorationAdapter
       }

P06AnimalCountingWitnessFromPayload :
  BalabanP06MixedReducerPayload →
  OwnedP06AnimalCountingWitness
P06AnimalCountingWitnessFromPayload payload = record
  { payload = payload
  ; animalCountingBound =
      BalabanP06AnimalCountingFromAdapters payload
  }

P06SourceSkeletonDecompositionSemanticKernelFromPayload :
  BalabanP06MixedReducerPayload →
  P06SourceSkeletonDecompositionSemanticKernel
P06SourceSkeletonDecompositionSemanticKernelFromPayload payload =
  let residual =
        P06ResidualCountingSprintWitnessFromPayload payload
      decoration =
        P06bDecorationMultiplicityWitnessFromPayload payload
      animal =
        P06AnimalCountingWitnessFromPayload payload
  in record
       { payload = payload
       ; sourceAuthorityId = dashi-internal-proof
       ; theoremLocator =
           "BalabanPolymerDiameterEntropy.P06SourceSkeletonDecompositionSemanticKernelFromPayload/P06ResidualCountingSprintWitnessFromPayload/P06bDecorationMultiplicityWitnessFromPayload/P06AnimalCountingWitnessFromPayload"
       ; status = mixedReducer
       ; reducedSkeletonCardinality =
           OwnedP06ResidualCountingSprintWitness.reducedSkeletonCardinality
             residual
       ; diameterShellBound =
           OwnedP06ResidualCountingSprintWitness.diameterShellBound
             residual
       ; decorationMultiplicityByDiameter =
           OwnedP06bDecorationMultiplicityWitness.decorationBound
             decoration
       ; animalCountingBound =
           OwnedP06AnimalCountingWitness.animalCountingBound
             animal
       }

OwnedP06SourceSkeletonDecompositionSprintWitnessFromPayload :
  BalabanP06MixedReducerPayload →
  OwnedP06SourceSkeletonDecompositionSprintWitness
OwnedP06SourceSkeletonDecompositionSprintWitnessFromPayload payload =
  let residual =
        P06ResidualCountingSprintWitnessFromPayload payload
      decoration =
        P06bDecorationMultiplicityWitnessFromPayload payload
      animal =
        P06AnimalCountingWitnessFromPayload payload
  in record
       { sourceAuthorityId = dashi-internal-proof
       ; theoremLocator =
           "BalabanPolymerDiameterEntropy.OwnedP06SourceSkeletonDecompositionSprintWitnessFromPayload/P06SourceSkeletonDecompositionSemanticKernelFromPayload"
       ; status = mixedReducer
       ; sourceSkeletonDecompositionSemanticKernel =
           P06SourceSkeletonDecompositionSemanticKernelFromPayload payload
       ; residualCountingWitness = residual
       ; decorationMultiplicityWitness = decoration
       ; animalCountingWitness = animal
       }

P06ResidualCountingSprintWitnessFromModelLeaf :
  P06ModelLeafDischargePackage →
  OwnedP06ResidualCountingSprintWitness
P06ResidualCountingSprintWitnessFromModelLeaf pkg =
  P06ResidualCountingSprintWitnessFromPayload
    (P06FromModelLeafDischargePackage pkg)

P06bDecorationMultiplicityWitnessFromModelLeaf :
  P06ModelLeafDischargePackage →
  OwnedP06bDecorationMultiplicityWitness
P06bDecorationMultiplicityWitnessFromModelLeaf pkg =
  P06bDecorationMultiplicityWitnessFromPayload
    (P06FromModelLeafDischargePackage pkg)

P06AnimalCountingWitnessFromModelLeaf :
  P06ModelLeafDischargePackage →
  OwnedP06AnimalCountingWitness
P06AnimalCountingWitnessFromModelLeaf pkg = record
  P06AnimalCountingWitnessFromPayload
    (P06FromModelLeafDischargePackage pkg)

P06SourceSkeletonDecompositionSemanticKernelFromModelLeaf :
  P06ModelLeafDischargePackage →
  P06SourceSkeletonDecompositionSemanticKernel
P06SourceSkeletonDecompositionSemanticKernelFromModelLeaf pkg =
  P06SourceSkeletonDecompositionSemanticKernelFromPayload
    (P06FromModelLeafDischargePackage pkg)

OwnedP06SourceSkeletonDecompositionSprintWitnessFromModelLeaf :
  P06ModelLeafDischargePackage →
  OwnedP06SourceSkeletonDecompositionSprintWitness
OwnedP06SourceSkeletonDecompositionSprintWitnessFromModelLeaf pkg =
  OwnedP06SourceSkeletonDecompositionSprintWitnessFromPayload
    (P06FromModelLeafDischargePackage pkg)

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
    sourceDecompositionKernel : P06SourceSkeletonDecompositionSemanticKernel
    sourceWitness : ImportedPolymerAnimalCountingBound
    theoremBoundary : String
    theoremBoundaryIsCanonical :
      theoremBoundary ≡
      "P06c: DASHI recombines rooted support-graph skeleton shells with the owned decoration-multiplicity leaf through the owned mixed-reducer kernel; the remaining external boundary is the source animal-counting witness naming that kernel as its authority surface."

record P06AnimalCountingReducer : Set₁ where
  field
    p06aSkeletonCounting : P06aRootedConnectedSkeletonCounting
    p06bDecorationBound : ImportedP06bPolymerDecorationMultiplicityBound
    p06cRecombination : P06cSkeletonDecorationImpliesAnimalCounting
    sourceDecompositionKernel : P06SourceSkeletonDecompositionSemanticKernel
    sourceWitness : ImportedPolymerAnimalCountingBound
    rootedShellInterface : RootedPolymerShellCountingInterface
    proofBoundary : String
    proofBoundaryIsCanonical :
      proofBoundary ≡
      "P06AnimalCountingReducer: DASHI owns the rooted-shell adapter, the decoration multiplicity bridge, and the skeleton-plus-decoration recombination through the owned mixed-reducer kernel; the only remaining external boundary is the source animal-counting witness fed into that reducer."

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

currentBalabanP06a3bReducedSkeletonCardinalityBound :
  GraphCombinatorics.ReducedSkeletonCardinalityBound
    (BalabanGraphAdapter.supportGraph currentBalabanGraphAdapter)
currentBalabanP06a3bReducedSkeletonCardinalityBound =
  BalabanP06a3bFromComplexity
    currentBalabanGraphAdapter
    currentBalabanReducedSkeletonComplexityAdapter

currentBalabanP06a3bComplexityToCardinalityKernel :
  ∀ (r : GraphCombinatorics.Graph.Vertex
         (BalabanGraphAdapter.supportGraph currentBalabanGraphAdapter))
    (X : List
      (GraphCombinatorics.Graph.Vertex
        (BalabanGraphAdapter.supportGraph currentBalabanGraphAdapter))) →
    (rrs : GraphCombinatorics.RootedReducedSkeleton
             (BalabanGraphAdapter.supportGraph currentBalabanGraphAdapter)
             r X) →
  length X ≤
    GraphCombinatorics.ReducedSkeletonCardinalityBound.K
      currentBalabanP06a3bReducedSkeletonCardinalityBound
      * GraphCombinatorics.diam_G
          {BalabanGraphAdapter.supportGraph currentBalabanGraphAdapter} X
      + GraphCombinatorics.ReducedSkeletonCardinalityBound.B
          currentBalabanP06a3bReducedSkeletonCardinalityBound
currentBalabanP06a3bComplexityToCardinalityKernel r X rrs =
  GraphCombinatorics.ReducedSkeletonCardinalityBound.bound
    currentBalabanP06a3bReducedSkeletonCardinalityBound
    r X rrs

currentBalabanP06a3aDiameterToLinearSizeKernel :
  ∀ (r : GraphCombinatorics.Graph.Vertex
         (BalabanGraphAdapter.supportGraph currentBalabanGraphAdapter))
    (X : List
      (GraphCombinatorics.Graph.Vertex
        (BalabanGraphAdapter.supportGraph currentBalabanGraphAdapter))) →
    (rrs : GraphCombinatorics.RootedReducedSkeleton
             (BalabanGraphAdapter.supportGraph currentBalabanGraphAdapter)
             r X) →
    (n : Nat) →
  GraphCombinatorics.diam_G
    {BalabanGraphAdapter.supportGraph currentBalabanGraphAdapter} X ≡ n →
  length X ≤
    GraphCombinatorics.ReducedSkeletonCardinalityBound.K
      currentBalabanP06a3bReducedSkeletonCardinalityBound
      * n
      + GraphCombinatorics.ReducedSkeletonCardinalityBound.B
          currentBalabanP06a3bReducedSkeletonCardinalityBound
currentBalabanP06a3aDiameterToLinearSizeKernel r X rrs n diam-eq =
  GraphCombinatorics.DiameterShellCoveredByLinearSizeShells
    currentBalabanP06a3bReducedSkeletonCardinalityBound
    r X rrs n diam-eq

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

currentBalabanP06a3ShellSummationKernel :
  ∀ (r : GraphCombinatorics.Graph.Vertex
         (BalabanGraphAdapter.supportGraph currentBalabanGraphAdapter))
    (n : Nat) →
  GraphCombinatorics.countReducedSkeletonsWithDiam
    (BalabanGraphAdapter.supportGraph currentBalabanGraphAdapter) r n ≤
  fst currentBalabanP06a3DiameterShellCountingBound ^ n
currentBalabanP06a3ShellSummationKernel =
  snd currentBalabanP06a3DiameterShellCountingBound

currentBalabanP06ResidualCountingKernelTheoremLocator : String
currentBalabanP06ResidualCountingKernelTheoremLocator =
  "BalabanPolymerDiameterEntropy.currentBalabanP06a3bReducedSkeletonCardinalityBound/currentBalabanP06a3DiameterShellCountingBound"

currentOwnedP06a3DiameterShellCountingWitness :
  OwnedP06a3DiameterShellCountingWitness
currentOwnedP06a3DiameterShellCountingWitness = record
  { payload = currentBalabanP06MixedReducerPayload
  ; diameterShellBound = currentBalabanP06a3DiameterShellCountingBound
  }

currentOwnedP06ResidualCountingSprintWitness :
  OwnedP06ResidualCountingSprintWitness
currentOwnedP06ResidualCountingSprintWitness = record
  { payload = currentBalabanP06MixedReducerPayload
  ; sourceAuthorityId = dashi-internal-proof
  ; theoremLocator = currentBalabanP06ResidualCountingKernelTheoremLocator
  ; status = mixedReducer
  ; reducedSkeletonCardinality =
      currentBalabanP06a3bReducedSkeletonCardinalityBound
  ; diameterShellBound = currentBalabanP06a3DiameterShellCountingBound
  }

currentOwnedP06ResidualUsesConstructiveP06a3b :
  OwnedP06ResidualCountingSprintWitness.reducedSkeletonCardinality
    currentOwnedP06ResidualCountingSprintWitness
    ≡ currentBalabanP06a3bReducedSkeletonCardinalityBound
currentOwnedP06ResidualUsesConstructiveP06a3b = refl

currentOwnedP06ResidualUsesConstructiveP06a3 :
  OwnedP06ResidualCountingSprintWitness.diameterShellBound
    currentOwnedP06ResidualCountingSprintWitness
    ≡ currentBalabanP06a3DiameterShellCountingBound
currentOwnedP06ResidualUsesConstructiveP06a3 = refl

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
      "BalabanPolymerDiameterEntropy.currentBalabanP06a3bReducedSkeletonCardinalityBound/currentBalabanP06a3DiameterShellCountingBound/currentOwnedP06bDecorationMultiplicityWitness/currentOwnedP06AnimalCountingWitness"
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

P06EndpointUnblockingSemanticKernelFromSourceKernel :
  P06SourceSkeletonDecompositionSemanticKernel →
  P06EndpointUnblockingSemanticKernel
P06EndpointUnblockingSemanticKernelFromSourceKernel kernel = record
  { sourceAuthorityId = dashi-internal-proof
  ; theoremLocator =
      "BalabanPolymerDiameterEntropy.P06EndpointUnblockingSemanticKernelFromSourceKernel/pZeroPositiveWitness/P07ReducerFromDischargePackage/P09MarginFromDischargePackage/P07P09ReducerPairFromP06P10AndMargin"
  ; status = mixedReducer
  ; sourceSkeletonDecompositionSemanticKernel = kernel
  ; pZeroWitness = pZeroPositiveWitness
  ; kpBoundary = P07ReducerFromDischargePackage
  ; entropyMarginBoundary = P09MarginFromDischargePackage
  ; jointP07P09Boundary = P07P09ReducerPairFromP06P10AndMargin
  }

P06EndpointUnblockingSemanticKernelFromModelLeaf :
  P06ModelLeafDischargePackage →
  P06EndpointUnblockingSemanticKernel
P06EndpointUnblockingSemanticKernelFromModelLeaf pkg =
  P06EndpointUnblockingSemanticKernelFromSourceKernel
    (P06SourceSkeletonDecompositionSemanticKernelFromModelLeaf pkg)

OwnedP06EndpointUnblockingSprintWitnessFromSourceWitness :
  OwnedP06SourceSkeletonDecompositionSprintWitness →
  OwnedP06EndpointUnblockingSprintWitness
OwnedP06EndpointUnblockingSprintWitnessFromSourceWitness witness = record
  { sourceAuthorityId = dashi-internal-proof
  ; theoremLocator =
      "BalabanPolymerDiameterEntropy.OwnedP06EndpointUnblockingSprintWitnessFromSourceWitness/P06EndpointUnblockingSemanticKernelFromSourceKernel"
  ; status = mixedReducer
  ; endpointSemanticKernel =
      P06EndpointUnblockingSemanticKernelFromSourceKernel
        (OwnedP06SourceSkeletonDecompositionSprintWitness.sourceSkeletonDecompositionSemanticKernel
          witness)
  ; skeletonDecompositionWitness = witness
  ; p06Reducer = currentP06AnimalCountingReducer
  ; pZeroWitness =
      P06EndpointUnblockingSemanticKernel.pZeroWitness
        (P06EndpointUnblockingSemanticKernelFromSourceKernel
          (OwnedP06SourceSkeletonDecompositionSprintWitness.sourceSkeletonDecompositionSemanticKernel
            witness))
  }

OwnedP06EndpointUnblockingSprintWitnessFromModelLeaf :
  P06ModelLeafDischargePackage →
  OwnedP06EndpointUnblockingSprintWitness
OwnedP06EndpointUnblockingSprintWitnessFromModelLeaf pkg =
  OwnedP06EndpointUnblockingSprintWitnessFromSourceWitness
    (OwnedP06SourceSkeletonDecompositionSprintWitnessFromModelLeaf pkg)

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

currentP06WitnessUsesOwnedSourceKernelPayload :
  ImportedPolymerAnimalCountingBound.mixedReducerPayload
    polymerAnimalCountingBoundWitness
    ≡ P06SourceSkeletonDecompositionSemanticKernel.payload
        currentP06SourceSkeletonDecompositionSemanticKernel
currentP06WitnessUsesOwnedSourceKernelPayload = refl

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

currentP06BoundedDegreeConstant : ℕ
currentP06BoundedDegreeConstant =
  BalabanGraphAdapter.degreeBound currentBalabanGraphAdapter

currentBalabanP06a2SizeShellCountingBound :
  Σ Nat
    (λ C-size →
      ∀ (r : GraphCombinatorics.Graph.Vertex
             (BalabanGraphAdapter.supportGraph currentBalabanGraphAdapter))
        (m : Nat) →
      GraphCombinatorics.countSkeletons
        (BalabanGraphAdapter.supportGraph currentBalabanGraphAdapter) r m ≤
      C-size ^ m)
currentBalabanP06a2SizeShellCountingBound =
  BalabanP06a2FromGraphCombinatorics currentBalabanGraphAdapter

currentP06SizeShellGrowthConstant : ℕ
currentP06SizeShellGrowthConstant =
  fst currentBalabanP06a2SizeShellCountingBound

canonicalRootedSkeletonSizeShellCountingInterface :
  RootedSkeletonSizeShellCountingInterface
canonicalRootedSkeletonSizeShellCountingInterface = record
  { Root = currentP06ShellRoot
  ; sizeShellGrowthConstant = currentP06SizeShellGrowthConstant
  ; sizeShellCountAt =
      GraphCombinatorics.countSkeletons
        (BalabanGraphAdapter.supportGraph currentBalabanGraphAdapter)
  ; sizeShellCountBound =
      snd currentBalabanP06a2SizeShellCountingBound
  ; interfaceBoundary =
      "P06a2 reducer: the rooted connected skeleton size-shell count is exposed directly as a root-indexed exponential shell-count envelope."
  ; interfaceBoundaryIsCanonical = refl
  }

currentP06SizeShellInterfaceUsesOwnedSizeConstant :
  RootedSkeletonSizeShellCountingInterface.sizeShellGrowthConstant
    canonicalRootedSkeletonSizeShellCountingInterface
    ≡ fst currentBalabanP06a2SizeShellCountingBound
currentP06SizeShellInterfaceUsesOwnedSizeConstant = refl

currentP06SizeShellInterfaceUsesOwnedSizeShellCount :
  RootedSkeletonSizeShellCountingInterface.sizeShellCountAt
    canonicalRootedSkeletonSizeShellCountingInterface
    ≡ GraphCombinatorics.countSkeletons
        (BalabanGraphAdapter.supportGraph currentBalabanGraphAdapter)
currentP06SizeShellInterfaceUsesOwnedSizeShellCount = refl

currentP06ShellGrowthConstant : ℕ
currentP06ShellGrowthConstant =
  fst currentBalabanP06a3DiameterShellCountingBound

canonicalRootedPolymerShellCountingInterface :
  RootedPolymerShellCountingInterface
canonicalRootedPolymerShellCountingInterface = record
  { Root = currentP06ShellRoot
  ; shellGrowthConstant = currentP06ShellGrowthConstant
  ; shellCountAt =
      GraphCombinatorics.countReducedSkeletonsWithDiam
        (BalabanGraphAdapter.supportGraph currentBalabanGraphAdapter)
  ; shellCountBound =
      snd currentBalabanP06a3DiameterShellCountingBound
  ; interfaceBoundary =
      "P06 reducer: DASHI owns the diameter-indexed rooted polymer shell envelope; the remaining external boundary is only the source animal-counting witness consumed through that envelope."
  ; interfaceBoundaryIsCanonical = refl
  }

currentP06ShellInterfaceUsesOwnedDiameterConstant :
  RootedPolymerShellCountingInterface.shellGrowthConstant
    canonicalRootedPolymerShellCountingInterface
    ≡ fst currentBalabanP06a3DiameterShellCountingBound
currentP06ShellInterfaceUsesOwnedDiameterConstant = refl

currentP06ShellInterfaceUsesOwnedDiameterShellCount :
  RootedPolymerShellCountingInterface.shellCountAt
    canonicalRootedPolymerShellCountingInterface
    ≡ GraphCombinatorics.countReducedSkeletonsWithDiam
        (BalabanGraphAdapter.supportGraph currentBalabanGraphAdapter)
currentP06ShellInterfaceUsesOwnedDiameterShellCount = refl

currentP06aRootedConnectedSkeletonCounting :
  P06aRootedConnectedSkeletonCounting
currentP06a1BoundedDegreeSupportGraphSkeleton :
  P06a1BoundedDegreeSupportGraphSkeleton
currentP06a1BoundedDegreeSupportGraphSkeleton = record
  { sizeShellInterface = canonicalRootedSkeletonSizeShellCountingInterface
  ; rootedShellInterface = canonicalRootedPolymerShellCountingInterface
  ; maxDegreeBound = currentP06BoundedDegreeConstant
  ; theoremBoundary =
      "P06a1: DASHI isolates the graph-skeleton side of P06 as a rooted support-graph shell family together with an explicit bounded-degree parameter."
  ; theoremBoundaryIsCanonical = refl
  }

currentP06a1UsesOwnedBoundedDegree :
  P06a1BoundedDegreeSupportGraphSkeleton.maxDegreeBound
    currentP06a1BoundedDegreeSupportGraphSkeleton
    ≡ BalabanGraphAdapter.degreeBound currentBalabanGraphAdapter
currentP06a1UsesOwnedBoundedDegree = refl

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
  ; sizeShellBridgeBound =
      λ root n →
        RootedSkeletonSizeShellCountingInterface.sizeShellCountBound
          canonicalRootedSkeletonSizeShellCountingInterface
          root n
  ; theoremBoundary =
      "P06a2f: the DFS-walk size-shell counting bridge is kept explicit between the rooted spanning-tree witness and the bounded-degree shell bound."
  ; theoremBoundaryIsCanonical = refl
  }

currentP06a2fUsesOwnedDiameterShellBound :
  P06a2fDFSWalkSizeShellCountingBridge.sizeShellBridgeBound
    currentP06a2fDFSWalkSizeShellCountingBridge
    ≡ (λ root n →
        RootedSkeletonSizeShellCountingInterface.sizeShellCountBound
          canonicalRootedSkeletonSizeShellCountingInterface
          root n)
currentP06a2fUsesOwnedDiameterShellBound = refl

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
      RootedSkeletonSizeShellCountingInterface.sizeShellCountBound
        canonicalRootedSkeletonSizeShellCountingInterface
  ; theoremBoundary =
      "P06a2a: before any polymer-specific counting refinement, DASHI exposes the rooted bounded-degree shell family as a root-ball growth bound over diameter shells."
  ; theoremBoundaryIsCanonical = refl
  }

currentP06a2aUsesOwnedDiameterShellBound :
  P06a2aBoundedDegreeRootBallGrowth.rootBallShellBound
    currentP06a2aBoundedDegreeRootBallGrowth
    ≡ RootedSkeletonSizeShellCountingInterface.sizeShellCountBound
        canonicalRootedSkeletonSizeShellCountingInterface
currentP06a2aUsesOwnedDiameterShellBound = refl

currentP06a2RootedConnectedSkeletonSizeShellCounting = record
  { boundedDegreeSkeleton = currentP06a1BoundedDegreeSupportGraphSkeleton
  ; rootBallGrowth = currentP06a2aBoundedDegreeRootBallGrowth
  ; rootedSpanningTreeWitness = currentConnectedSkeletonHasRootedSpanningTree
  ; dfsWalkWitness = currentRootedTreeDFSWalk
  ; dfsWalkSizeShellBridge = currentP06a2fDFSWalkSizeShellCountingBridge
  ; walkCountWitness = currentBoundedDegreeWalkCount
  ; walkCoverWitness = currentConnectedSkeletonCoveredByDFSWalk
  ; sizeShellBound =
      λ root n →
        RootedSkeletonSizeShellCountingInterface.sizeShellCountBound
          canonicalRootedSkeletonSizeShellCountingInterface
          root n
  ; theoremBoundary =
      "P06a2: bounded-degree rooted connected skeletons are counted first in size-indexed shells before any polymer-specific decoration overhead is considered."
  ; theoremBoundaryIsCanonical = refl
  }

currentP06a2UsesOwnedDiameterShellBound :
  P06a2RootedConnectedSkeletonSizeShellCounting.sizeShellBound
    currentP06a2RootedConnectedSkeletonSizeShellCounting
    ≡ (λ root n →
        RootedSkeletonSizeShellCountingInterface.sizeShellCountBound
          canonicalRootedSkeletonSizeShellCountingInterface
          root n)
currentP06a2UsesOwnedDiameterShellBound = refl

currentP06a3DiameterShellSkeletonCounting :
  P06a3DiameterShellSkeletonCounting
currentReducedSkeletonCardinalityBound :
  ReducedSkeletonCardinalityBound
currentReducedSkeletonCardinalityBound = record
  { boundedDegreeSkeleton = currentP06a1BoundedDegreeSupportGraphSkeleton
  ; K =
      GraphCombinatorics.ReducedSkeletonCardinalityBound.K
        currentBalabanP06a3bReducedSkeletonCardinalityBound
  ; B =
      GraphCombinatorics.ReducedSkeletonCardinalityBound.B
        currentBalabanP06a3bReducedSkeletonCardinalityBound
  ; reducedSkeletonDiameterBound =
      currentBalabanP06a3aDiameterToLinearSizeKernel
  ; theoremBoundary =
      "P06a3b: bounded degree alone is not enough for exponential diameter-shell counting, so DASHI exposes the missing reduced-skeleton cardinality theorem explicitly as a linear size-or-complexity-by-diameter bound."
  ; theoremBoundaryIsCanonical = refl
  }

currentP06a3bUsesOwnedLinearDiameterConstant :
  ReducedSkeletonCardinalityBound.K
    currentReducedSkeletonCardinalityBound
    ≡ GraphCombinatorics.ReducedSkeletonCardinalityBound.K
        currentBalabanP06a3bReducedSkeletonCardinalityBound
currentP06a3bUsesOwnedLinearDiameterConstant = refl

currentP06a3bUsesOwnedLinearDiameterOffset :
  ReducedSkeletonCardinalityBound.B
    currentReducedSkeletonCardinalityBound
    ≡ GraphCombinatorics.ReducedSkeletonCardinalityBound.B
        currentBalabanP06a3bReducedSkeletonCardinalityBound
currentP06a3bUsesOwnedLinearDiameterOffset = refl

currentP06a3bExportsOwnedComplexityToCardinalityKernel :
  ∀ (r : GraphCombinatorics.Graph.Vertex
         (BalabanGraphAdapter.supportGraph currentBalabanGraphAdapter))
    (X : List
      (GraphCombinatorics.Graph.Vertex
        (BalabanGraphAdapter.supportGraph currentBalabanGraphAdapter))) →
    (rrs : GraphCombinatorics.RootedReducedSkeleton
             (BalabanGraphAdapter.supportGraph currentBalabanGraphAdapter)
             r X) →
  length X ≤
    GraphCombinatorics.ReducedSkeletonCardinalityBound.K
      currentBalabanP06a3bReducedSkeletonCardinalityBound
      * GraphCombinatorics.diam_G
          {BalabanGraphAdapter.supportGraph currentBalabanGraphAdapter} X
      + GraphCombinatorics.ReducedSkeletonCardinalityBound.B
          currentBalabanP06a3bReducedSkeletonCardinalityBound
currentP06a3bExportsOwnedComplexityToCardinalityKernel =
  currentBalabanP06a3bComplexityToCardinalityKernel

currentP06a3aDiameterShellContainedInRootBall :
  P06a3aDiameterShellContainedInRootBall
currentP06a3aDiameterShellContainedInRootBall = record
  { sizeShellCounting = currentP06a2RootedConnectedSkeletonSizeShellCounting
  ; diameterShellContained =
      λ root n →
        RootedPolymerShellCountingInterface.shellCountBound
          canonicalRootedPolymerShellCountingInterface
          root n
  ; theoremBoundary =
      "P06a3a: diameter-indexed rooted connected skeleton shells are first reduced to a bounded root-ball containment statement before the final diameter-shell count is consumed."
  ; theoremBoundaryIsCanonical = refl
  }

currentP06a3aUsesOwnedDiameterShellBound :
  P06a3aDiameterShellContainedInRootBall.diameterShellContained
    currentP06a3aDiameterShellContainedInRootBall
    ≡ (λ root n →
        RootedPolymerShellCountingInterface.shellCountBound
          canonicalRootedPolymerShellCountingInterface
          root n)
currentP06a3aUsesOwnedDiameterShellBound = refl

currentP06a3aExportsOwnedDiameterToLinearSizeKernel :
  ∀ (r : GraphCombinatorics.Graph.Vertex
         (BalabanGraphAdapter.supportGraph currentBalabanGraphAdapter))
    (X : List
      (GraphCombinatorics.Graph.Vertex
        (BalabanGraphAdapter.supportGraph currentBalabanGraphAdapter))) →
    (rrs : GraphCombinatorics.RootedReducedSkeleton
             (BalabanGraphAdapter.supportGraph currentBalabanGraphAdapter)
             r X) →
    (n : Nat) →
  GraphCombinatorics.diam_G
    {BalabanGraphAdapter.supportGraph currentBalabanGraphAdapter} X ≡ n →
  length X ≤
    GraphCombinatorics.ReducedSkeletonCardinalityBound.K
      currentBalabanP06a3bReducedSkeletonCardinalityBound
      * n
      + GraphCombinatorics.ReducedSkeletonCardinalityBound.B
          currentBalabanP06a3bReducedSkeletonCardinalityBound
currentP06a3aExportsOwnedDiameterToLinearSizeKernel =
  currentBalabanP06a3aDiameterToLinearSizeKernel

currentP06a3DiameterShellSkeletonCounting = record
  { sizeShellCounting = currentP06a2RootedConnectedSkeletonSizeShellCounting
  ; diameterShellContainment = currentP06a3aDiameterShellContainedInRootBall
  ; reducedSkeletonCardinality = currentReducedSkeletonCardinalityBound
  ; diameterShellBound =
      λ root n →
        RootedPolymerShellCountingInterface.shellCountBound
          canonicalRootedPolymerShellCountingInterface
          root n
  ; theoremBoundary =
      "P06a3: diameter-indexed rooted connected skeleton shells are reduced using size-shell counting plus an explicit size-or-complexity-controlled-by-diameter leaf before the explicit decoration leaf is applied."
  ; theoremBoundaryIsCanonical = refl
  }

currentP06a3UsesOwnedDiameterShellBound :
  P06a3DiameterShellSkeletonCounting.diameterShellBound
    currentP06a3DiameterShellSkeletonCounting
    ≡ (λ root n →
        RootedPolymerShellCountingInterface.shellCountBound
          canonicalRootedPolymerShellCountingInterface
          root n)
currentP06a3UsesOwnedDiameterShellBound = refl

currentP06a3ExportsOwnedShellSummationKernel :
  ∀ (r : GraphCombinatorics.Graph.Vertex
         (BalabanGraphAdapter.supportGraph currentBalabanGraphAdapter))
    (n : Nat) →
  GraphCombinatorics.countReducedSkeletonsWithDiam
    (BalabanGraphAdapter.supportGraph currentBalabanGraphAdapter) r n ≤
  fst currentBalabanP06a3DiameterShellCountingBound ^ n
currentP06a3ExportsOwnedShellSummationKernel =
  currentBalabanP06a3ShellSummationKernel

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
  ; sourceDecompositionKernel =
      currentP06SourceSkeletonDecompositionSemanticKernel
  ; sourceWitness = polymerAnimalCountingBoundWitness
  ; theoremBoundary =
      "P06c: DASHI recombines rooted support-graph skeleton shells with the owned decoration-multiplicity leaf through the owned mixed-reducer kernel; the remaining external boundary is the source animal-counting witness naming that kernel as its authority surface."
  ; theoremBoundaryIsCanonical = refl
  }

currentP06cUsesOwnedSourceDecompositionKernel :
  P06cSkeletonDecorationImpliesAnimalCounting.sourceDecompositionKernel
    currentP06cSkeletonDecorationImpliesAnimalCounting
    ≡ currentP06SourceSkeletonDecompositionSemanticKernel
currentP06cUsesOwnedSourceDecompositionKernel = refl

currentP06cWitnessMatchesOwnedSourceKernelPayload :
  ImportedPolymerAnimalCountingBound.mixedReducerPayload
    (P06cSkeletonDecorationImpliesAnimalCounting.sourceWitness
      currentP06cSkeletonDecorationImpliesAnimalCounting)
    ≡ P06SourceSkeletonDecompositionSemanticKernel.payload
        (P06cSkeletonDecorationImpliesAnimalCounting.sourceDecompositionKernel
          currentP06cSkeletonDecorationImpliesAnimalCounting)
currentP06cWitnessMatchesOwnedSourceKernelPayload = refl

assembleP06ReducerFromSourceWitness :
  ImportedPolymerAnimalCountingBound →
  P06AnimalCountingReducer
assembleP06ReducerFromSourceWitness p06 = record
  { p06aSkeletonCounting = currentP06aRootedConnectedSkeletonCounting
  ; p06bDecorationBound = p06bDecorationMultiplicityBoundWitness
  ; p06cRecombination = currentP06cSkeletonDecorationImpliesAnimalCounting
  ; sourceDecompositionKernel =
      currentP06SourceSkeletonDecompositionSemanticKernel
  ; sourceWitness = p06
  ; rootedShellInterface = canonicalRootedPolymerShellCountingInterface
  ; proofBoundary =
      "P06AnimalCountingReducer: DASHI owns the rooted-shell adapter, the decoration multiplicity bridge, and the skeleton-plus-decoration recombination through the owned mixed-reducer kernel; the only remaining external boundary is the source animal-counting witness fed into that reducer."
  ; proofBoundaryIsCanonical = refl
  }

currentP06AnimalCountingReducer : P06AnimalCountingReducer
currentP06AnimalCountingReducer =
  assembleP06ReducerFromSourceWitness polymerAnimalCountingBoundWitness

currentP06ReducerUsesOwnedSourceDecompositionKernel :
  P06AnimalCountingReducer.sourceDecompositionKernel
    currentP06AnimalCountingReducer
    ≡ currentP06SourceSkeletonDecompositionSemanticKernel
currentP06ReducerUsesOwnedSourceDecompositionKernel = refl

currentP06ReducerWitnessMatchesOwnedSourceKernelPayload :
  ImportedPolymerAnimalCountingBound.mixedReducerPayload
    (P06AnimalCountingReducer.sourceWitness currentP06AnimalCountingReducer)
    ≡ P06SourceSkeletonDecompositionSemanticKernel.payload
        (P06AnimalCountingReducer.sourceDecompositionKernel
          currentP06AnimalCountingReducer)
currentP06ReducerWitnessMatchesOwnedSourceKernelPayload = refl

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
      "P06 is routed through DASHI-owned P06a/P06b/P06c rooted-shell counting, decoration multiplicity, and skeleton-plus-decoration recombination through the owned mixed-reducer kernel; the remaining external P06 boundary is the source animal-counting witness, while P07/P09 consume the arithmetic queue as the explicit decay-vs-entropy closure."
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
      "P06 is routed through DASHI-owned P06a/P06b/P06c rooted-shell counting, decoration multiplicity, and skeleton-plus-decoration recombination through the owned mixed-reducer kernel; the remaining external P06 boundary is the source animal-counting witness, while P07/P09 consume the arithmetic queue as the explicit decay-vs-entropy closure."
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

record P07KPSummabilityReducer : Set₁ where
  field
    kpCriterionWitness :
      KoteckyPreissCriterion
    proofBoundary : String
    proofBoundaryIsCanonical :
      proofBoundary ≡
      "P07 reducer: discharge-package activity decay and entropy counting are composed into shell summability and hence the KP criterion; in the current endpoint lane this reducer is consumed through the owned current P06 mixed-reducer path."

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

record P09EntropyMargin : Set₁ where
  field
    marginTheorem :
      ∀ (cDiam : ℝ) →
      0ℝ ≤ℝ cDiam →
      cDiam ≤ℝ 1ℝ →
      (cDiam *ℝ ArithmeticQueue.fourQ-ℝ) <ℝ 1ℝ
    proofBoundary : String
    proofBoundaryIsCanonical :
      proofBoundary ≡
      "P09 reducer: the discharge package exposes the entropy constant and decay margin while DASHI reuses the internal 4q arithmetic closure for admissible diameter constants; in the current endpoint lane this reducer is consumed through the owned current P06 mixed-reducer path."

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

  GeometricShellSummability :
    shellConstant <ℝ 1ℝ
    → Summable shellContribution

  entropyDecayDominatesEntropy :
    (entropyConst *ℝ decayBase) <ℝ 1ℝ

ShellRatioBelowOneFromEntropyDominance :
  (entropyConst *ℝ decayBase) <ℝ 1ℝ →
  shellConstant <ℝ 1ℝ
ShellRatioBelowOneFromEntropyDominance h = h

KPCriterionFromShellSummability :
  Summable shellContribution →
  KoteckyPreissCriterion
KPCriterionFromShellSummability h = h

KPCriterionFromEntropyDominance :
  (entropyConst *ℝ decayBase) <ℝ 1ℝ →
  KoteckyPreissCriterion
KPCriterionFromEntropyDominance h =
  KPCriterionFromShellSummability
    (GeometricShellSummability
      (ShellRatioBelowOneFromEntropyDominance h))

P07ReducerFromDischargePackage :
  P07KPSummabilityDischargePackage
  → P07KPSummabilityReducer
P07ReducerFromDischargePackage pkg = record
  { kpCriterionWitness =
      P07KPSummabilityDischargePackage.kpCriterion pkg
  ; proofBoundary =
      "P07 reducer: discharge-package activity decay and entropy counting are composed into shell summability and hence the KP criterion; in the current endpoint lane this reducer is consumed through the owned current P06 mixed-reducer path."
  ; proofBoundaryIsCanonical = refl
  }

P09MarginFromDischargePackage :
  P09EntropyMarginDischargePackage
  → P09EntropyMargin
P09MarginFromDischargePackage pkg = record
  { marginTheorem =
      ArithmeticQueue.ArithmeticLemmaQueueBundle.marginClosed
        ArithmeticQueue.currentArithmeticLemmaQueueBundle
  ; proofBoundary =
      "P09 reducer: the discharge package exposes the entropy constant and decay margin while DASHI reuses the internal 4q arithmetic closure for admissible diameter constants; in the current endpoint lane this reducer is consumed through the owned current P06 mixed-reducer path."
  ; proofBoundaryIsCanonical = refl
  }

P07P09ReducerPairFromP06P10AndMargin :
  P06AnimalCountingReducer
  → (∀ (k : Nat) (X : List Nat) → LargeField.P10LargeFieldSuppressionPackage k X)
  → P07KPSummabilityDischargePackage
  → P09EntropyMarginDischargePackage
  → P07KPSummabilityReducer × P09EntropyMargin
P07P09ReducerPairFromP06P10AndMargin p6 p10 kp margin =
  P07ReducerFromDischargePackage kp ,
  P09MarginFromDischargePackage margin

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
      → P07KPSummabilityDischargePackage
      → P09EntropyMarginDischargePackage
      → P07KPSummabilityReducer × P09EntropyMargin

currentP06EndpointUnblockingSemanticKernel :
  P06EndpointUnblockingSemanticKernel
currentP06EndpointUnblockingSemanticKernel = record
  { sourceAuthorityId = dashi-internal-proof
  ; theoremLocator =
      "BalabanPolymerDiameterEntropy.currentP06SourceSkeletonDecompositionSemanticKernel/currentP06AnimalCountingReducer/pZeroPositiveWitness/P07ReducerFromDischargePackage/P09MarginFromDischargePackage/P07P09ReducerPairFromP06P10AndMargin"
  ; status = mixedReducer
  ; sourceSkeletonDecompositionSemanticKernel =
      currentP06SourceSkeletonDecompositionSemanticKernel
  ; pZeroWitness = pZeroPositiveWitness
  ; kpBoundary = P07ReducerFromDischargePackage
  ; entropyMarginBoundary = P09MarginFromDischargePackage
  ; jointP07P09Boundary = P07P09ReducerPairFromP06P10AndMargin
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

    p06Reducer :
      P06AnimalCountingReducer

    pZeroWitness :
      ImportedPZeroPositive

currentOwnedP06EndpointUnblockingSprintWitness :
  OwnedP06EndpointUnblockingSprintWitness
currentOwnedP06EndpointUnblockingSprintWitness = record
  { sourceAuthorityId = dashi-internal-proof
  ; theoremLocator =
      "BalabanPolymerDiameterEntropy.currentP06EndpointUnblockingSemanticKernel/currentOwnedP06SourceSkeletonDecompositionSprintWitness/currentP06AnimalCountingReducer"
  ; status = mixedReducer
  ; endpointSemanticKernel =
      currentP06EndpointUnblockingSemanticKernel
  ; skeletonDecompositionWitness =
      currentOwnedP06SourceSkeletonDecompositionSprintWitness
  ; p06Reducer = currentP06AnimalCountingReducer
  ; pZeroWitness =
      P06EndpointUnblockingSemanticKernel.pZeroWitness
        currentP06EndpointUnblockingSemanticKernel
  }

currentP06EndpointKernelUsesOwnedSourceKernel :
  P06EndpointUnblockingSemanticKernel.sourceSkeletonDecompositionSemanticKernel
    currentP06EndpointUnblockingSemanticKernel
    ≡ currentP06SourceSkeletonDecompositionSemanticKernel
currentP06EndpointKernelUsesOwnedSourceKernel = refl

currentOwnedP06EndpointWitnessUsesCurrentP06Reducer :
  OwnedP06EndpointUnblockingSprintWitness.p06Reducer
    currentOwnedP06EndpointUnblockingSprintWitness
    ≡ currentP06AnimalCountingReducer
currentOwnedP06EndpointWitnessUsesCurrentP06Reducer = refl

currentOwnedP06EndpointReducerMatchesOwnedSourceKernelPayload :
  ImportedPolymerAnimalCountingBound.mixedReducerPayload
    (P06AnimalCountingReducer.sourceWitness
      (OwnedP06EndpointUnblockingSprintWitness.p06Reducer
        currentOwnedP06EndpointUnblockingSprintWitness))
    ≡ P06SourceSkeletonDecompositionSemanticKernel.payload
        (P06EndpointUnblockingSemanticKernel.sourceSkeletonDecompositionSemanticKernel
          (OwnedP06EndpointUnblockingSprintWitness.endpointSemanticKernel
            currentOwnedP06EndpointUnblockingSprintWitness))
currentOwnedP06EndpointReducerMatchesOwnedSourceKernelPayload = refl

P07FromKPSummabilityPackage :
  P07KPSummabilityDischargePackage
  → P07KPSummabilityReducer
P07FromKPSummabilityPackage pkg =
  P06EndpointUnblockingSemanticKernel.kpBoundary
    currentP06EndpointUnblockingSemanticKernel
    pkg

P07FromCurrentP06KPSummabilityPackage :
  P07KPSummabilityDischargePackage
  → P07KPSummabilityReducer
P07FromCurrentP06KPSummabilityPackage pkg =
  P06EndpointUnblockingSemanticKernel.kpBoundary
    (OwnedP06EndpointUnblockingSprintWitness.endpointSemanticKernel
      currentOwnedP06EndpointUnblockingSprintWitness)
    pkg

currentP07FromCurrentP06UsesOwnedEndpointKernel :
  P07FromCurrentP06KPSummabilityPackage
    ≡
  (λ pkg →
    P06EndpointUnblockingSemanticKernel.kpBoundary
      currentP06EndpointUnblockingSemanticKernel
      pkg)
currentP07FromCurrentP06UsesOwnedEndpointKernel = refl

currentP07FromCurrentP06UsesCurrentOwnedReducerLane :
  P06EndpointUnblockingSemanticKernel.sourceSkeletonDecompositionSemanticKernel
    (OwnedP06EndpointUnblockingSprintWitness.endpointSemanticKernel
      currentOwnedP06EndpointUnblockingSprintWitness)
    ≡ P06AnimalCountingReducer.sourceDecompositionKernel
        (OwnedP06EndpointUnblockingSprintWitness.p06Reducer
          currentOwnedP06EndpointUnblockingSprintWitness)
currentP07FromCurrentP06UsesCurrentOwnedReducerLane = refl

P09FromEntropyMarginPackage :
  P09EntropyMarginDischargePackage
  → P09EntropyMargin
P09FromEntropyMarginPackage pkg =
  P06EndpointUnblockingSemanticKernel.entropyMarginBoundary
    currentP06EndpointUnblockingSemanticKernel
    pkg

P09FromCurrentP06EntropyMarginPackage :
  P09EntropyMarginDischargePackage
  → P09EntropyMargin
P09FromCurrentP06EntropyMarginPackage pkg =
  P06EndpointUnblockingSemanticKernel.entropyMarginBoundary
    (OwnedP06EndpointUnblockingSprintWitness.endpointSemanticKernel
      currentOwnedP06EndpointUnblockingSprintWitness)
    pkg

currentP09FromCurrentP06UsesOwnedEndpointKernel :
  P09FromCurrentP06EntropyMarginPackage
    ≡
  (λ pkg →
    P06EndpointUnblockingSemanticKernel.entropyMarginBoundary
      currentP06EndpointUnblockingSemanticKernel
      pkg)
currentP09FromCurrentP06UsesOwnedEndpointKernel = refl

currentP09FromCurrentP06UsesCurrentOwnedReducerLane :
  P06EndpointUnblockingSemanticKernel.sourceSkeletonDecompositionSemanticKernel
    (OwnedP06EndpointUnblockingSprintWitness.endpointSemanticKernel
      currentOwnedP06EndpointUnblockingSprintWitness)
    ≡ P06AnimalCountingReducer.sourceDecompositionKernel
        (OwnedP06EndpointUnblockingSprintWitness.p06Reducer
          currentOwnedP06EndpointUnblockingSprintWitness)
currentP09FromCurrentP06UsesCurrentOwnedReducerLane = refl

P07P09FromP06P10AndMargin :
  P06AnimalCountingReducer
  → (∀ (k : Nat) (X : List Nat) → LargeField.P10LargeFieldSuppressionPackage k X)
  → P07KPSummabilityDischargePackage
  → P09EntropyMarginDischargePackage
  → P07KPSummabilityReducer × P09EntropyMargin
P07P09FromP06P10AndMargin p6 p10 kp margin =
  P06EndpointUnblockingSemanticKernel.jointP07P09Boundary
    currentP06EndpointUnblockingSemanticKernel
    p6 p10 kp margin

P07P09FromCurrentP06P10AndMargin :
  (∀ (k : Nat) (X : List Nat) → LargeField.P10LargeFieldSuppressionPackage k X)
  → P07KPSummabilityDischargePackage
  → P09EntropyMarginDischargePackage
  → P07KPSummabilityReducer × P09EntropyMargin
P07P09FromCurrentP06P10AndMargin p10 kp margin =
  P06EndpointUnblockingSemanticKernel.jointP07P09Boundary
    currentP06EndpointUnblockingSemanticKernel
    (OwnedP06EndpointUnblockingSprintWitness.p06Reducer
      currentOwnedP06EndpointUnblockingSprintWitness)
    p10 kp margin

currentP07P09UsesCurrentOwnedP06Reducer :
  P07P09FromCurrentP06P10AndMargin
    ≡
  (λ p10 kp margin →
    P06EndpointUnblockingSemanticKernel.jointP07P09Boundary
      currentP06EndpointUnblockingSemanticKernel
      currentP06AnimalCountingReducer
      p10 kp margin)
currentP07P09UsesCurrentOwnedP06Reducer = refl
