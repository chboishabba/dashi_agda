module DASHI.SexedHistoricalReopenableSynthesisValidation where

open import DASHI.Core.Prelude

import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Core.EpistemicSuspensionExact as Suspension
import DASHI.Core.AffectedDependencyClosureExact as Dependency
import DASHI.Governance.SexedHistoricalProductiveDialecticalFibreJoinExact as Join
import DASHI.Governance.SexedHistoricalDialecticalJoinAdaptiveSearchExact as Search
import DASHI.Governance.SexedHistoricalReopenableSynthesisEndOfHistoryBoundaryExact as Reopen
import DASHI.Governance.SexedHistoricalSelectiveReopeningExact as Selective

productiveJoinNextHistoryRegression :
  INF.FactorsThrough Reopen.joinPresentSurface Reopen.nextContinuation → ⊥
productiveJoinNextHistoryRegression =
  Reopen.productiveJoinSurfaceCannotRecoverNextHistory

productiveJoinHasOutgoingTransitionRegression :
  Reopen.JoinTransport Reopen.productiveJoinAtT Reopen.counterformationAtNext
productiveJoinHasOutgoingTransitionRegression =
  Reopen.canonicalJoinHasOutgoingTransport

productiveJoinAcceptedNowRegression :
  Join.joinDisposition Join.productiveJoin ≡ Suspension.acceptHere
productiveJoinAcceptedNowRegression = Reopen.currentJoinAcceptedAsProductive

historicalFinalityStillOpenRegression :
  Reopen.finalityDisposition Reopen.finalityUnresolved
  ≡ Suspension.suspendAndRefine
historicalFinalityStillOpenRegression =
  Reopen.historicalFinalityRemainsUnresolvedInCanonicalFixture

selectivePowerGateReopeningRegression :
  Dependency.ReopeningObligation
    Selective.Depends
    Selective.counterformationResidual
    Selective.powerGateCertificate
selectivePowerGateReopeningRegression = Selective.powerGateMustReopen

selectiveNextJoinSearchReopeningRegression :
  Dependency.ReopeningObligation
    Selective.Depends
    Selective.counterformationResidual
    Selective.nextJoinSearchCertificate
selectiveNextJoinSearchReopeningRegression = Selective.nextJoinSearchMustReopen

reopenedSearchMeasurementRegression :
  Search.nextJoinMeasurement
    Search.verifyStrictAffordanceExpansion
    (Join.joinDisposition Join.unresolvedJoin)
  ≡ Search.optionConeProbe
reopenedSearchMeasurementRegression =
  Selective.reopenedJoinSearchSelectsAffordanceProbe

selectiveReopeningBoundaryRegression :
  Selective.SelectiveHistoricalReopeningBoundary
selectiveReopeningBoundaryRegression =
  Selective.canonicalSelectiveHistoricalReopeningBoundary

canonicalSourceBoundaryRegression :
  Reopen.ReopenableSynthesisEndOfHistoryBoundary
canonicalSourceBoundaryRegression =
  Reopen.canonicalReopenableSynthesisEndOfHistoryBoundary
