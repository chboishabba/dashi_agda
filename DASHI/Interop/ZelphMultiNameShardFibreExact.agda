module DASHI.Interop.ZelphMultiNameShardFibreExact where

-- A1: collision-preserving physical name fibres, never a fabricated
-- singleton. The actual published bytes/whole name domain must still be
-- enumerated independently to construct this complete fibre record.

open import DASHI.Core.Prelude
import DASHI.Interop.ZelphPhysicalShardQueryMaxCutExact as Singleton

infix 4 _∈Fibre_
data _∈Fibre_ {Shard : Set} (shard : Shard) : List Shard → Set where
  atHead : ∀ {tail} → shard ∈Fibre (shard ∷ tail)
  inTail : ∀ {head tail} → shard ∈Fibre tail → shard ∈Fibre (head ∷ tail)

record CompleteNameShardFibre (Key Shard : Set)
    (contains : Key → Shard → Set) : Set₁ where
  field
    shardFibre : Key → List Shard
    noMissingShard :
      (key : Key) (shard : Shard) →
      contains key shard → shard ∈Fibre (shardFibre key)
    noFabricatedShard :
      (key : Key) (shard : Shard) →
      shard ∈Fibre (shardFibre key) → contains key shard

open CompleteNameShardFibre public

zelphDuplicateNameFibreExhaustive :
  ∀ {Key Shard : Set}
    {contains : Key → Shard → Set} →
  (cert : CompleteNameShardFibre Key Shard contains) →
  (key : Key) (shard : Shard) →
  (contains key shard → shard ∈Fibre (shardFibre cert key)) ×
  (shard ∈Fibre (shardFibre cert key) → contains key shard)
zelphDuplicateNameFibreExhaustive cert key shard =
  noMissingShard cert key shard , noFabricatedShard cert key shard

-- A globally unique key is a special case of the collision-capable carrier.
-- The reverse implication requires a genuine original-source uniqueness
-- argument, not merely one successful QID lookup or sorted-chunk assumption.
singletonNameFibre :
  ∀ {Key Shard : Set}
    {route : Key → Shard}
    {contains : Key → Shard → Set} →
  Singleton.NameShardPartition Key Shard route contains →
  CompleteNameShardFibre Key Shard contains
singletonNameFibre {Key = Key} {Shard = Shard}
  {route = route} {contains = contains} cert = record
  { shardFibre = λ key → route key ∷ []
  ; noMissingShard = λ key shard proof →
      subst (λ candidate → candidate ∈Fibre (route key ∷ []))
            (sym (Singleton.indexedExclusivity cert key shard proof))
            atHead
  ; noFabricatedShard = singletonSound
  }
  where
    singletonSound :
      (key : Key) (shard : Shard) →
      shard ∈Fibre (route key ∷ []) → contains key shard
    singletonSound key .(route key) atHead = Singleton.indexedCoverage cert key
    singletonSound key shard (inTail ())
