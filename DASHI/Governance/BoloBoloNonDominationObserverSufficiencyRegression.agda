module DASHI.Governance.BoloBoloNonDominationObserverSufficiencyRegression where

open import DASHI.Core.Prelude

import DASHI.Governance.BoloBoloNonDominationObserverSufficiencyExact as ND

efficiencyCapacityObserverBlocked :
  ND.efficiencyCapacityObserverConsumerSufficient
    ND.canonicalNonDominationObserverBoundary ≡ false
efficiencyCapacityObserverBlocked = refl

realizedControlLeastSufficientPaid :
  ND.realizedControlConsumerLeastSufficientPaid
    ND.canonicalNonDominationObserverBoundary ≡ true
realizedControlLeastSufficientPaid = refl

allAdequateRefineRealizedControl :
  ND.everyRealizedControlAdequateObserverRefinesCanonicalPaid
    ND.canonicalNonDominationObserverBoundary ≡ true
allAdequateRefineRealizedControl = refl

samePerformanceNotSamePower :
  ND.sameCoordinationPerformanceDoesNotDetermineRealizedControl
    ND.canonicalNonDominationObserverBoundary ≡ true
samePerformanceNotSamePower = refl

syntheticNotEmpirical :
  ND.syntheticCollisionCreatesEmpiricalNonDominationResult
    ND.canonicalNonDominationObserverBoundary ≡ false
syntheticNotEmpirical = refl
