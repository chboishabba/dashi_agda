module DASHI.Governance.BoloBoloCapacityConsumerSufficiencyRegression where

open import DASHI.Core.Prelude

import DASHI.Governance.BoloBoloCapacityConsumerSufficiencyExact as Capacity

leastObserverPaid :
  Capacity.capacityConsumerLeastSufficientPaid Capacity.canonicalCapacityConsumerBoundary ≡ true
leastObserverPaid = refl

durationBlocked :
  Capacity.durationObserverConsumerSufficient Capacity.canonicalCapacityConsumerBoundary ≡ false
durationBlocked = refl

durationIncidenceBlocked :
  Capacity.durationIncidenceObserverConsumerSufficient Capacity.canonicalCapacityConsumerBoundary ≡ false
durationIncidenceBlocked = refl

allAdequateObserversRefineCapacityConsumer :
  Capacity.everyCapacityAdequateObserverRefinesCanonicalPaid Capacity.canonicalCapacityConsumerBoundary ≡ true
allAdequateObserversRefineCapacityConsumer = refl

syntheticOnly :
  Capacity.syntheticWitnessCreatesEmpiricalCapacityResult Capacity.canonicalCapacityConsumerBoundary ≡ false
syntheticOnly = refl
