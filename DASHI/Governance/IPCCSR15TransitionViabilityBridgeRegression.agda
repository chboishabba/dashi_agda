module DASHI.Governance.IPCCSR15TransitionViabilityBridgeRegression where

open import DASHI.Core.Prelude

import DASHI.Governance.IPCCSR15TransitionViabilityBridgeExact as Bridge

rapidFarReachingTransitionsAreSourceAttributed :
  Bridge.rapidFarReachingSystemTransitions Bridge.canonicalSR15SourceBoundary ≡ true
rapidFarReachingTransitionsAreSourceAttributed = refl

portfolioTradeoffsAreSourceAttributed :
  Bridge.mitigationPortfolioHasSynergiesAndTradeoffs Bridge.canonicalSR15SourceBoundary ≡ true
portfolioTradeoffsAreSourceAttributed = refl

lowDemandSynergyIsQualified :
  Bridge.lowEnergyDemandPathwaysHaveStrongSDSynergies Bridge.canonicalSR15SourceBoundary ≡ true
lowDemandSynergyIsQualified = refl

sr15DoesNotProveFederationViable :
  Bridge.sr15ProvesFederatedGovernanceViable Bridge.canonicalSR15BridgeBoundary ≡ false
sr15DoesNotProveFederationViable = refl

sr15DoesNotProveBoloBolo :
  Bridge.sr15ProvesBoloBoloMeetsClimateTargets Bridge.canonicalSR15BridgeBoundary ≡ false
sr15DoesNotProveBoloBolo = refl
