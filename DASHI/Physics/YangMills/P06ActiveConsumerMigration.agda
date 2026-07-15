module DASHI.Physics.YangMills.P06ActiveConsumerMigration where

------------------------------------------------------------------------
-- P06 consumer projections.
--
-- `P06ActiveConsumer` below is retained as the legacy exact-(n + n)
-- compatibility surface.  `P06OwnedActiveConsumer` is the preferred route:
-- it constructs the exact Euler-DFS injection internally and exposes only
-- finite count semantics, undirected adjacency, and a positive degree bound.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Nat.Base using (ℕ; _∸_; _+_; _≤_; _*_) 

open import DASHI.Physics.ClaySupportingElementaryLemmas using (pow)

open import DASHI.Physics.YangMills.GraphCombinatorics as GC
  using ( Graph
        ; BoundedNeighbourEnumeration
        ; CanonicalSkeletonEnumeration
        ; ConcreteCountSkeletonsSemantics
        ; CountWalksMembershipSemantics
        ; FiniteBallEnumeration
        ; ActualSkeletonEncodingData
        ; countSkeletons
        )

open import DASHI.Physics.YangMills.P06ConcreteEnumerationEndpoint as Endpoint
  using ( P06ConcreteEnumerationEndpoint )

open import DASHI.Physics.YangMills.P06DFSValidWalkSurface as DFS
  using ( DFSValidWalkMapWitness )
open import DASHI.Physics.YangMills.P06ConstructiveSpanningTreeDFS
  using ( UndirectedGraphStructure )
open import DASHI.Physics.YangMills.P06ConcreteEnumerationEndpoint
  using ( CanonicalBoundedNeighbourEnumerationWithDegree )
open import DASHI.Physics.YangMills.P06ExactEnumerationEndpoint as Exact
  using ( P06ConcreteCountSemantics
        ; P06ConcreteEnumerationTheoremOwned
        )

------------------------------------------------------------------------
-- Legacy exact-(n + n) compatibility consumer.  New consumers should use
-- `P06OwnedActiveConsumer` below.
------------------------------------------------------------------------

record P06ActiveConsumer
  {G : Graph} {Δ : ℕ} {r : Graph.Vertex G} {n : ℕ}
  (FBE : FiniteBallEnumeration G r (n ∸ 1)) : Set₁ where
  field
    endpoint : P06ConcreteEnumerationEndpoint {Δ = Δ} {n = n} FBE

------------------------------------------------------------------------
-- Legacy exact-(n + n) DFS-input boundary.
------------------------------------------------------------------------

record P06ActiveDFSInput
  {G : Graph} {Δ : ℕ} {r : Graph.Vertex G} {n : ℕ}
  (CE : CanonicalSkeletonEnumeration G r n)
  (BNE : BoundedNeighbourEnumeration G Δ)
  (WE : CountWalksMembershipSemantics G r (n + n)) : Set₁ where
  field
    witness : DFSValidWalkMapWitness CE BNE WE

------------------------------------------------------------------------
-- Direct endpoint projections.
------------------------------------------------------------------------

activeEndpoint :
  {G : Graph} {Δ : ℕ} {r : Graph.Vertex G} {n : ℕ}
  {FBE : FiniteBallEnumeration G r (n ∸ 1)}
  (consumer : P06ActiveConsumer {Δ = Δ} {n = n} FBE) →
  P06ConcreteEnumerationEndpoint {Δ = Δ} {n = n} FBE
activeEndpoint {G = G} {Δ = Δ} {r = r} {n = n} {FBE = FBE} consumer =
  P06ActiveConsumer.endpoint consumer

activeSkeletonSemantics :
  {G : Graph} {Δ : ℕ} {r : Graph.Vertex G} {n : ℕ}
  {FBE : FiniteBallEnumeration G r (n ∸ 1)}
  (consumer : P06ActiveConsumer {Δ = Δ} {n = n} FBE) →
  ConcreteCountSkeletonsSemantics G r n FBE
activeSkeletonSemantics {G = G} {Δ = Δ} {r = r} {n = n} {FBE = FBE} consumer =
  P06ConcreteEnumerationEndpoint.skeletonSemantics
    (P06ActiveConsumer.endpoint consumer)

activeWalkSemantics :
  {G : Graph} {Δ : ℕ} {r : Graph.Vertex G} {n : ℕ}
  {FBE : FiniteBallEnumeration G r (n ∸ 1)}
  (consumer : P06ActiveConsumer {Δ = Δ} {n = n} FBE) →
  CountWalksMembershipSemantics G r (n + n)
activeWalkSemantics {G = G} {Δ = Δ} {r = r} {n = n} {FBE = FBE} consumer =
  P06ConcreteEnumerationEndpoint.walkSemantics
    (P06ActiveConsumer.endpoint consumer)

activeEncodingData :
  {G : Graph} {Δ : ℕ} {r : Graph.Vertex G} {n : ℕ}
  {FBE : FiniteBallEnumeration G r (n ∸ 1)}
  (consumer : P06ActiveConsumer {Δ = Δ} {n = n} FBE) →
  ActualSkeletonEncodingData G r n
activeEncodingData {G = G} {Δ = Δ} {r = r} {n = n} {FBE = FBE} consumer =
  P06ConcreteEnumerationEndpoint.encodingData
    (P06ActiveConsumer.endpoint consumer)

activeSkeletonCountBound :
  {G : Graph} {Δ : ℕ} {r : Graph.Vertex G} {n : ℕ}
  {FBE : FiniteBallEnumeration G r (n ∸ 1)}
  (consumer : P06ActiveConsumer {Δ = Δ} {n = n} FBE) →
  countSkeletons G r n ≤ pow (Δ * Δ) n
activeSkeletonCountBound {G = G} {Δ = Δ} {r = r} {n = n} {FBE = FBE} consumer =
  P06ConcreteEnumerationEndpoint.countBound
    (P06ActiveConsumer.endpoint consumer)

activeEncodingDataIsEndpointData :
  {G : Graph} {Δ : ℕ} {r : Graph.Vertex G} {n : ℕ}
  {FBE : FiniteBallEnumeration G r (n ∸ 1)}
  (consumer : P06ActiveConsumer {Δ = Δ} {n = n} FBE) →
  P06ConcreteEnumerationEndpoint.encodingData
    (activeEndpoint consumer)
    ≡ activeEncodingData consumer
activeEncodingDataIsEndpointData
  {G = G} {Δ = Δ} {r = r} {n = n} {FBE = FBE} consumer = refl

------------------------------------------------------------------------
-- Exact-length owned consumer.  This is the preferred new surface: unlike
-- P06ActiveConsumer, it neither carries a legacy n+n DFS map nor exposes
-- any traversal implementation witness.
------------------------------------------------------------------------

record P06OwnedActiveConsumer
  {G : Graph} {Δ : ℕ} {r : Graph.Vertex G} {n : ℕ}
  (FBE : FiniteBallEnumeration G r (n ∸ 1)) : Set₁ where
  field
    undirected : UndirectedGraphStructure G
    positiveΔ : 1 ≤ Δ
    neighbourEnumeration :
      CanonicalBoundedNeighbourEnumerationWithDegree G Δ
    skeletonEnumeration :
      GC.ExplicitSkeletonCandidateEnumeration G r n FBE
    countSemantics :
      P06ConcreteCountSemantics
        FBE neighbourEnumeration skeletonEnumeration

open P06OwnedActiveConsumer public

ownedActiveSkeletonCountBound :
  {G : Graph} {Δ : ℕ} {r : Graph.Vertex G} {n : ℕ}
  {FBE : FiniteBallEnumeration G r (n ∸ 1)}
  (consumer : P06OwnedActiveConsumer {Δ = Δ} {n = n} FBE) →
  countSkeletons G r n ≤ pow (Δ * Δ) n
ownedActiveSkeletonCountBound
  {G = G} {Δ = Δ} {r = r} {n = n} {FBE = FBE} consumer =
  P06ConcreteEnumerationTheoremOwned
    FBE
    (undirected consumer)
    (positiveΔ consumer)
    (neighbourEnumeration consumer)
    (skeletonEnumeration consumer)
    (countSemantics consumer)
