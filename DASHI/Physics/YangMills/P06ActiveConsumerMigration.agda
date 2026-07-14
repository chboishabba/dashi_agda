module DASHI.Physics.YangMills.P06ActiveConsumerMigration where

------------------------------------------------------------------------
-- Additive active-consumer projection for P06.
--
-- The endpoint is accepted as the exact remaining P06 input.  This keeps
-- the migration compiling while the dependent equality between a concrete
-- canonical skeleton enumeration and a DFS witness is still open.  No
-- legacy total `CountWalksSemantics` record is imported or constructed.
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

------------------------------------------------------------------------
-- The live additive consumer: all downstream projections consume this
-- endpoint and therefore stay on the membership-indexed walk surface.
------------------------------------------------------------------------

record P06ActiveConsumer
  {G : Graph} {Δ : ℕ} {r : Graph.Vertex G} {n : ℕ}
  (FBE : FiniteBallEnumeration G r (n ∸ 1)) : Set₁ where
  field
    endpoint : P06ConcreteEnumerationEndpoint {Δ = Δ} {n = n} FBE

------------------------------------------------------------------------
-- Exact DFS input boundary for a future endpoint constructor.  CE is kept
-- explicit: forcing it to be definitionally equal to the endpoint's
-- derived canonical enumeration is the remaining dependent bridge.
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
