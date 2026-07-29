module DASHI.Codec.DNADeBruijnCapacity where

open import Agda.Builtin.List using (List)
open import Agda.Builtin.Nat using (Nat)

open import DASHI.Codec.DNAFirstFormalism using (Base)
open import DASHI.Codec.DNAProductionConstraints using (ProductionState)
open import DASHI.Codec.DNAProductionDeBruijn using
  ( Edge; Reachable; outDegree )

------------------------------------------------------------------------
-- Exact finite extraction is a receipt, not an assumption hidden in matrix
-- notation. A concrete extractor must enumerate every reachable state and edge.

record FiniteReachableGraph : Set₁ where
  field
    vertices : List ProductionState
    edgeLabels : ProductionState → List Base
    vertexComplete : ∀ s → Reachable s → Set
    edgeComplete :
      ∀ {s b t} → Edge s b t → Reachable s → Set
    degreeAgreement : ∀ s → outDegree s ≡ length (edgeLabels s)
  where
  length : ∀ {X : Set} → List X → Nat
  length [] = 0
  length (_ ∷ xs) = Nat.suc (length xs)

------------------------------------------------------------------------
-- Strongly connected recurrent cores and Eulerian coverage require explicit
-- graph evidence. They are not consequences of local admissibility alone.

record StronglyConnectedCore (G : FiniteReachableGraph) : Set₁ where
  field
    coreVertices : List ProductionState
    nonEmpty : Set
    mutuallyReachable : Set
    closedUnderOutgoing : Set

record EulerianCoreReceipt (G : FiniteReachableGraph) : Set₁ where
  field
    core : StronglyConnectedCore G
    balancedDegrees : Set
    connectedSupport : Set
    universalCycle : List Base
    traversesEveryCoreEdgeExactlyOnce : Set

------------------------------------------------------------------------
-- Capacity is conditional on a concrete finite adjacency representation and a
-- certified Perron root. The executable extractor may estimate it numerically;
-- no floating-point estimate is promoted into an Agda equality.

record PerronCapacityReceipt (G : FiniteReachableGraph) : Set₁ where
  field
    Scalar : Set
    adjacency : Set
    lambda : Scalar
    lambdaIsPerronRoot : Set
    log2 : Scalar → Scalar
    bitsPerBase : Scalar
    capacityDefinition : bitsPerBase ≡ log2 lambda

record CapacityComparison : Set₁ where
  field
    Scalar : Set
    measuredRate : Scalar
    constrainedCapacity : Scalar
    rateDoesNotExceedCapacity : Set
    codingGap : Scalar
    gapDefinition : Set
