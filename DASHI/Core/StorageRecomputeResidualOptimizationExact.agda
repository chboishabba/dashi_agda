module DASHI.Core.StorageRecomputeResidualOptimizationExact where

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- Residual optimization with recomputation.
--
-- A deployment may store a larger residual and reopen cheaply, or store less
-- and reconstruct omitted state by bounded recomputation.  Description/storage
-- cost and reopening compute cost are therefore independent coordinates.
------------------------------------------------------------------------

record ReopeningPlan : Set where
  constructor reopeningPlan
  field
    storageCost : Nat
    recomputeCost : Nat

open ReopeningPlan public

weightedCost : Nat → ReopeningPlan → Nat
weightedCost weight plan = storageCost plan + weight * recomputeCost plan

record ReopeningSufficient (plan : ReopeningPlan) : Set where
  constructor reopeningSufficient

open ReopeningSufficient public

record CertifiedPlan : Set where
  constructor certifiedPlan
  field
    plan : ReopeningPlan
    sufficient : ReopeningSufficient plan

open CertifiedPlan public

record OptimalCertifiedPlan (weight : Nat) (chosen : CertifiedPlan) : Set where
  constructor optimalCertifiedPlan
  field
    noMoreExpensive :
      (candidate : CertifiedPlan) →
      weightedCost weight (plan chosen) ≤ weightedCost weight (plan candidate)

open OptimalCertifiedPlan public

------------------------------------------------------------------------
-- Finite cache/recompute family.
-- Costs are an exact toy model, not measurements from DeepSeek-V4.
------------------------------------------------------------------------

data CacheStrategy : Set where
  fullCache periodicCheckpoint zeroCache : CacheStrategy

strategyPlan : CacheStrategy → ReopeningPlan
strategyPlan fullCache = reopeningPlan 3 0
strategyPlan periodicCheckpoint = reopeningPlan 1 1
strategyPlan zeroCache = reopeningPlan 0 3

strategyIsSufficient : (strategy : CacheStrategy) → ReopeningSufficient (strategyPlan strategy)
strategyIsSufficient strategy = reopeningSufficient

certifiedStrategy : CacheStrategy → CertifiedPlan
certifiedStrategy strategy = certifiedPlan (strategyPlan strategy) (strategyIsSufficient strategy)

unitWeight : Nat
unitWeight = 1

fullCacheCost : weightedCost unitWeight (strategyPlan fullCache) ≡ 3
fullCacheCost = refl

checkpointCost : weightedCost unitWeight (strategyPlan periodicCheckpoint) ≡ 2
checkpointCost = refl

zeroCacheCost : weightedCost unitWeight (strategyPlan zeroCache) ≡ 3
zeroCacheCost = refl

checkpointNoWorseThanAnyStrategy :
  (strategy : CacheStrategy) →
  weightedCost unitWeight (strategyPlan periodicCheckpoint)
  ≤ weightedCost unitWeight (strategyPlan strategy)
checkpointNoWorseThanAnyStrategy fullCache =
  s≤s (s≤s (s≤s z≤n))
checkpointNoWorseThanAnyStrategy periodicCheckpoint = ≤-refl
checkpointNoWorseThanAnyStrategy zeroCache =
  s≤s (s≤s (s≤s z≤n))

checkpointIsOptimalInFiniteFamily :
  (strategy : CacheStrategy) →
  weightedCost unitWeight (strategyPlan periodicCheckpoint)
  ≤ weightedCost unitWeight (strategyPlan strategy)
checkpointIsOptimalInFiniteFamily = checkpointNoWorseThanAnyStrategy

------------------------------------------------------------------------
-- Trade-off boundary: minimal storage need not minimize deployment cost.
------------------------------------------------------------------------

zeroCacheHasLeastStorage : storageCost (strategyPlan zeroCache) ≡ 0
zeroCacheHasLeastStorage = refl

zeroCacheNotCheaperThanCheckpoint :
  weightedCost unitWeight (strategyPlan zeroCache)
  ≡ suc (weightedCost unitWeight (strategyPlan periodicCheckpoint))
zeroCacheNotCheaperThanCheckpoint = refl

-- Thus optimizing only L(delta) can select zeroCache, while optimizing
-- L(delta) + lambda * T_R(delta) selects periodicCheckpoint in this family.
