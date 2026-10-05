module DASHI.Governance.ConsensusDemocracyNonFactorabilityRegression where

open import DASHI.Core.Prelude

import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Governance.ConsensusDemocracyNonFactorabilityExact as C

sameConsensusCannotRecoverDemocraticProfile :
  INF.FactorsThrough C.consensusObserver C.democraticProfile → ⊥
sameConsensusCannotRecoverDemocraticProfile =
  C.consensusCannotDetermineDemocraticProfile

consensusIsNotDefinitionallyDemocracy :
  C.consensusAloneDeterminesDemocracy
    C.canonicalConsensusDemocracyBoundary
  ≡ false
consensusIsNotDefinitionallyDemocracy = refl

exitContestabilityRemainsIndependent :
  C.exitContestabilityIndependentOfConsensus
    C.canonicalConsensusDemocracyBoundary
  ≡ true
exitContestabilityRemainsIndependent = refl
