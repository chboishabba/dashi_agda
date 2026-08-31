module DASHI.Cognition.PNF.SetwiseAdjacentReconciliationDispatchExact where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- E1: batching adjacent reconciliation does not assert pair commutation.
--
-- Adjacency alone licenses neither semantic resolution nor independent updates.
-- The optimized physical path therefore preserves the declared ordered
-- sequential fold exactly, but dispatches that fold as one bounded database
-- tranche.  Pair i+1 is executed only after pair i in the semantic sequence.
------------------------------------------------------------------------

record OrderedAdjacentTrancheExecution
    (Pair Authority : Set) : Set₁ where
  field
    executeOne : Authority → Pair → Authority
    executeTwoTranche : Authority → Pair → Pair → Authority

    orderedTrancheExact :
      (authority : Authority) →
      (first second : Pair) →
      executeTwoTranche authority first second
        ≡
      executeOne (executeOne authority first) second

open OrderedAdjacentTrancheExecution public

------------------------------------------------------------------------
-- Physical work receipt.
--
-- The semantic fibre count remains P, but claim, dispatch and commit are
-- bounded by tranche count rather than pair count.  No theorem here says that
-- adjacent pairs commute or may be evaluated in parallel.
------------------------------------------------------------------------

record AdjacentTrancheWorkReceipt : Set where
  constructor adjacentTrancheWorkReceipt
  field
    pairCount : Nat
    trancheCount : Nat
    leaseBatchCount : Nat
    serverDispatchStatementCount : Nat
    authorityTransactionCount : Nat
    perPairClientRoundTripCount : Nat
    perPairCommitCount : Nat
    noRequiredPerPairClientRoundTrip : perPairClientRoundTripCount ≡ zero
    noRequiredPerPairCommit : perPairCommitCount ≡ zero

open AdjacentTrancheWorkReceipt public

------------------------------------------------------------------------
-- Atomicity is a physical publication boundary: partial success inside a
-- failed tranche is not authoritative.  It does not weaken the durable
-- work-item fence; retry still uses the existing per-work-item token/epoch.
------------------------------------------------------------------------

data AdjacentTrancheAllowsPartialFailedPublication : Set where

data AdjacentTrancheImpliesPairCommutation : Set where

data AdjacentTrancheImpliesDemandResolution : Set where

data AdjacentTrancheRequiresPerPairCommit : Set where

failedAdjacentTrancheCannotPublishPrefix :
  AdjacentTrancheAllowsPartialFailedPublication → ⊥
failedAdjacentTrancheCannotPublishPrefix ()

batchDispatchDoesNotProvePairCommutation :
  AdjacentTrancheImpliesPairCommutation → ⊥
batchDispatchDoesNotProvePairCommutation ()

batchDispatchDoesNotResolveByAdjacency :
  AdjacentTrancheImpliesDemandResolution → ⊥
batchDispatchDoesNotResolveByAdjacency ()

adjacentTrancheNeedNotCommitPerPair :
  AdjacentTrancheRequiresPerPairCommit → ⊥
adjacentTrancheNeedNotCommitPerPair ()
