module DASHI.Codec.DNADeBruijnCapacity where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)

open import DASHI.Codec.DNAFirstFormalism using (Base)
open import DASHI.Codec.DNAProductionConstraints using (ProductionState)
open import DASHI.Codec.DNAProductionDeBruijn using
  ( Edge; Reachable; outDegree )

length : ∀ {X : Set} → List X → Nat
length [] = zero
length (_ ∷ xs) = suc (length xs)

record FiniteReachableGraph : Set₁ where
  field
    vertices : List ProductionState
    edgeLabels : ProductionState → List Base
    vertexComplete : ∀ s → Reachable s → Set
    edgeComplete :
      ∀ {s b t} → Edge s b t → Reachable s → Set
    degreeAgreement : ∀ s → outDegree s ≡ length (edgeLabels s)

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
