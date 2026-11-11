{-# OPTIONS --safe #-}
module DASHI.Reasoning.FederatedMinerWorkerTopologyExact where

-- Finite topology specimen for the user's miner/worker MoE federation:
-- model -> expert -> six width-512 subexperts -> miner -> workers.
-- Economic miner ownership is NOT equated with machine identity.
-- No external runtime, CID hash, WAN timing, or trained neural correctness
-- is claimed by these finite graph/routing/arithmetic witnesses.

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Agda.Builtin.Equality using (_≡_; refl)

data Node : Set where
  coordinator minerEast minerWest : Node
  eastA eastB westA westB : Node

data Link : Node → Node → Set where
  toEast : Link coordinator minerEast
  toWest : Link coordinator minerWest
  eastWorkerA : Link minerEast eastA
  eastWorkerB : Link minerEast eastB
  westWorkerA : Link minerWest westA
  westWorkerB : Link minerWest westB
  crossMinerReplica : Link minerWest eastB

-- Reflexive/transitive directed reachability, not physical link availability.
data Reach : Node → Node → Set where
  here : {n : Node} → Reach n n
  hop  : {a b c : Node} → Link a b → Reach b c → Reach a c

eastAReachable : Reach coordinator eastA
eastAReachable = hop toEast (hop eastWorkerA here)

westAReachable : Reach coordinator westA
westAReachable = hop toWest (hop westWorkerA here)

eastBReachableViaOwnMiner : Reach coordinator eastB
eastBReachableViaOwnMiner = hop toEast (hop eastWorkerB here)

eastBReachableViaAlternateMiner : Reach coordinator eastB
eastBReachableViaAlternateMiner =
  hop toWest (hop crossMinerReplica here)

-- Node owner and dispatch parent are not assumed to be identical.
data Miner : Set where
  eastProvider westProvider : Miner

economicOwner : Node → Miner
economicOwner coordinator = eastProvider
economicOwner minerEast = eastProvider
economicOwner minerWest = westProvider
economicOwner eastA = eastProvider
economicOwner eastB = eastProvider
economicOwner westA = westProvider
economicOwner westB = westProvider

-- One 3072-dimensional intermediate axis, split into six 512-wide
-- shards, for the historical proposed K3-like 3072 axis ONLY.
-- This is not a universal Qwen model-width statement.
data Shard : Set where
  s0 s1 s2 s3 s4 s5 : Shard

shardWidth : Shard → Nat
shardWidth _ = 512

totalShardWidth : Nat
totalShardWidth = 512 + (512 + (512 + (512 + (512 + 512))))

six512ShardsCover3072 : totalShardWidth ≡ 3072
six512ShardsCover3072 = refl

-- Two worker endpoints own three shards each in this toy placement.
-- Real placement should be revisioned, capacity-tested and scheduled.
place : Shard → Node
place s0 = eastA
place s1 = eastA
place s2 = eastA
place s3 = westA
place s4 = westA
place s5 = westA

placementReachable : (s : Shard) → Reach coordinator (place s)
placementReachable s0 = eastAReachable
placementReachable s1 = eastAReachable
placementReachable s2 = eastAReachable
placementReachable s3 = westAReachable
placementReachable s4 = westAReachable
placementReachable s5 = westAReachable

-- Full shard coverage is expressed by the total lookup, not by
-- asserting that a finite test proves arbitrary dynamic topologies.
shardValue : Shard → Nat
shardValue s0 = 1
shardValue s1 = 2
shardValue s2 = 3
shardValue s3 = 4
shardValue s4 = 5
shardValue s5 = 6

-- Two miners can reduce their local shards concurrently. The coordinator
-- combines the resulting unweighted partials in this fixed order.
eastPartial : (Shard → Nat) → Nat
eastPartial f = f s0 + (f s1 + f s2)

westPartial : (Shard → Nat) → Nat
westPartial f = f s3 + (f s4 + f s5)

hierarchicalReduce : (Shard → Nat) → Nat
hierarchicalReduce f = eastPartial f + westPartial f

referenceReduce : (Shard → Nat) → Nat
referenceReduce f =
  (f s0 + (f s1 + f s2)) + (f s3 + (f s4 + f s5))

-- Exact for any supplied shard results (not a floating associativity
-- statement; real kernels need numerical error bounds).
hierarchicalAggregationEqualsReference :
  (f : Shard → Nat) →
  hierarchicalReduce f ≡ referenceReduce f
hierarchicalAggregationEqualsReference f = refl

concreteFanoutResult : hierarchicalReduce shardValue ≡ 21
concreteFanoutResult = refl

-- A fixed two-branch makespan witness: fanout completion is the slower
-- branch, unlike serial addition. All times are abstract natural units.
maxNat : Nat → Nat → Nat
maxNat zero n = n
maxNat (suc m) zero = suc m
maxNat (suc m) (suc n) = suc (maxNat m n)

parallelBranchCost : Nat
parallelBranchCost = maxNat 5 7

serialBranchCost : Nat
serialBranchCost = 5 + 7

parallelExampleIsSeven : parallelBranchCost ≡ 7
parallelExampleIsSeven = refl

serialExampleIsTwelve : serialBranchCost ≡ 12
serialExampleIsTwelve = refl

-- This finite example is not a theorem that federation always wins.
-- Network RTT, boundary serialization, contention, failure, energy and
-- availability can reverse the example.

-- Replica routing changes parent without changing the endpoint; this
-- demonstrates that peer reachability and authority are different axes.
data DispatchParent : Set where
  primary backup : DispatchParent

chooseParent : DispatchParent → Node
chooseParent primary = minerEast
chooseParent backup = minerWest

selectedReplicaEndpoint : DispatchParent → Node
selectedReplicaEndpoint _ = eastB

replicaDestinationUnchanged :
  selectedReplicaEndpoint primary ≡ selectedReplicaEndpoint backup
replicaDestinationUnchanged = refl

-- A per-shard CID, model revision, encoding and history witness is
-- still needed before the alternate route can be admitted in practice.
