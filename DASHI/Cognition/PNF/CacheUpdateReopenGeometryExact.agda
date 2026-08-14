module DASHI.Cognition.PNF.CacheUpdateReopenGeometryExact where

------------------------------------------------------------------------
-- CACHE / RUNTIME REPRESENTATION OBJECTIVES
--
-- Equal storage and equal output distortion do not determine update geometry
-- or reopening cost.  This is the finite exact counterpart of the proposed
-- storage + future distortion + transition/update + reopen objective.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

record CacheObjectives : Set where
  constructor cacheObjectives
  field
    storageCost : Nat
    futureOutputDistortion : Nat
    updateCost : Nat
    reopenCost : Nat

open CacheObjectives public

record SameStorageAndOutput (left right : CacheObjectives) : Set where
  field
    sameStorage : storageCost left ≡ storageCost right
    sameOutputDistortion :
      futureOutputDistortion left ≡ futureOutputDistortion right

open SameStorageAndOutput public

record OperationallyBetterAtSameSemanticCost
    (better worse : CacheObjectives) : Set where
  field
    sameSemanticCost : SameStorageAndOutput better worse
    updateNoWorse : updateCost better ≤ updateCost worse
    reopenNoWorse : reopenCost better ≤ reopenCost worse

open OperationallyBetterAtSameSemanticCost public

data CacheScheme : Set where globalRewrite localDelta : CacheScheme

objectives : CacheScheme → CacheObjectives
objectives globalRewrite = cacheObjectives 8 0 8 4
objectives localDelta = cacheObjectives 8 0 1 1

sameStorageAndOutput :
  SameStorageAndOutput (objectives localDelta) (objectives globalRewrite)
sameStorageAndOutput = record
  { sameStorage = refl
  ; sameOutputDistortion = refl
  }

localDeltaStrictlyLowersUpdateCost :
  updateCost (objectives localDelta) < updateCost (objectives globalRewrite)
localDeltaStrictlyLowersUpdateCost =
  s≤s (s≤s z≤n)

localDeltaStrictlyLowersReopenCost :
  reopenCost (objectives localDelta) < reopenCost (objectives globalRewrite)
localDeltaStrictlyLowersReopenCost =
  s≤s (s≤s z≤n)

localDeltaOperationallyBetter :
  OperationallyBetterAtSameSemanticCost
    (objectives localDelta) (objectives globalRewrite)
localDeltaOperationallyBetter = record
  { sameSemanticCost = sameStorageAndOutput
  ; updateNoWorse = ≤-trans (s≤s z≤n) localDeltaStrictlyLowersUpdateCost
  ; reopenNoWorse = ≤-trans (s≤s z≤n) localDeltaStrictlyLowersReopenCost
  }

------------------------------------------------------------------------
-- Weighted finite objective.  The weights are explicit consumer choices; no
-- universal weighting is asserted.
------------------------------------------------------------------------

weightedObjective : Nat → Nat → Nat → Nat → CacheObjectives → Nat
weightedObjective wStorage wFuture wUpdate wReopen c =
  wStorage * storageCost c
  + wFuture * futureOutputDistortion c
  + wUpdate * updateCost c
  + wReopen * reopenCost c

canonicalGlobalScore : weightedObjective 1 1 1 1 (objectives globalRewrite) ≡ 20
canonicalGlobalScore = refl

canonicalLocalScore : weightedObjective 1 1 1 1 (objectives localDelta) ≡ 10
canonicalLocalScore = refl

canonicalLocalStrictlyBetter :
  weightedObjective 1 1 1 1 (objectives localDelta)
  < weightedObjective 1 1 1 1 (objectives globalRewrite)
canonicalLocalStrictlyBetter =
  s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))))))

------------------------------------------------------------------------
-- The numbers are a regression witness, not empirical DeepSeek/LLM cache
-- measurements.  The theorem is the objective separation itself.
------------------------------------------------------------------------
