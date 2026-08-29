module DASHI.Analysis.RiemannAristotleWindowSchurCrossProverRegression where

open import DASHI.Core.Prelude

import DASHI.Analysis.ResidualBudgetMarginCompilerExact as Budget
import DASHI.Analysis.RiemannAristotleWindowSchurCrossProverSyncExact as Sync
import DASHI.Analysis.RiemannAristotleSharedWindowCertificateExact as Shared
import DASHI.Analysis.CertifiedFiniteCarrierReindexExact as Reindex

leanProofRemainsDistinctFromAgdaProof :
  Sync.AristotleAgdaSyncBoundary.leanProofIsAgdaProof
    Sync.canonicalAristotleAgdaSyncBoundary ≡ false
leanProofRemainsDistinctFromAgdaProof = refl

absoluteMassMajorizationRetired :
  Sync.AristotleAgdaSyncBoundary.absoluteMassMajorizationStillPreferred
    Sync.canonicalAristotleAgdaSyncBoundary ≡ false
absoluteMassMajorizationRetired = refl

schurBeforeTailMajorization :
  Sync.AristotleAgdaSyncBoundary.selectedNuisanceSchurBeforeTailMajorization
    Sync.canonicalAristotleAgdaSyncBoundary ≡ true
schurBeforeTailMajorization = refl

residualSignNotRequired :
  Sync.AristotleAgdaSyncBoundary.residualSignTheoremRequired
    Sync.canonicalAristotleAgdaSyncBoundary ≡ false
residualSignNotRequired = refl

normalizedEndpointTransportStillOpen :
  Sync.AristotleAgdaSyncBoundary.normalizedEndpointTransportClosed
    Sync.canonicalAristotleAgdaSyncBoundary ≡ false
normalizedEndpointTransportStillOpen = refl

riemannHypothesisStillNotDerived :
  Sync.AristotleAgdaSyncBoundary.riemannHypothesisDerived
    Sync.canonicalAristotleAgdaSyncBoundary ≡ false
riemannHypothesisStillNotDerived = refl

directMarginComparisonPreferred :
  Budget.ResidualBudgetMarginBoundary.directMarginComparisonPreferred
    Budget.canonicalResidualBudgetMarginBoundary ≡ true
directMarginComparisonPreferred = refl

residualNeedNotBeNonPositive :
  Budget.ResidualBudgetMarginBoundary.residualMustBeNonPositive
    Budget.canonicalResidualBudgetMarginBoundary ≡ false
residualNeedNotBeNonPositive = refl

sharedWindowConstructedOnce :
  Shared.SharedWindowBudgetCutset.windowConstructionSharedOnce
    Shared.canonicalSharedWindowBudgetCutset ≡ true
sharedWindowConstructedOnce = refl

sharedResponseEnvelopeConstructedOnce :
  Shared.SharedWindowBudgetCutset.responseEnvelopeSharedOnce
    Shared.canonicalSharedWindowBudgetCutset ≡ true
sharedResponseEnvelopeConstructedOnce = refl

oneSymbolicEndpointComparisonRemains :
  Shared.SharedWindowBudgetCutset.oneSymbolicBudgetComparisonRemains
    Shared.canonicalSharedWindowBudgetCutset ≡ true
oneSymbolicEndpointComparisonRemains = refl

endpointComparisonNotFabricated :
  Shared.SharedWindowBudgetCutset.endpointComparisonDerivedHere
    Shared.canonicalSharedWindowBudgetCutset ≡ false
endpointComparisonNotFabricated = refl

parallelAbstractCarrierRejected :
  Reindex.CertifiedCarrierReindexBoundary.estimateParallelAbstractCarrierInstead
    Reindex.canonicalCertifiedCarrierReindexBoundary ≡ false
parallelAbstractCarrierRejected = refl

exactReindexPreferred :
  Reindex.CertifiedCarrierReindexBoundary.exactReindexBeforeInnerEstimatePreferred
    Reindex.canonicalCertifiedCarrierReindexBoundary ≡ true
exactReindexPreferred = refl

boolReindexRoundTripFalse :
  Reindex.ExactCarrierReindex.decode Reindex.boolSwapReindex
    (Reindex.ExactCarrierReindex.encode Reindex.boolSwapReindex false) ≡ false
boolReindexRoundTripFalse = refl

boolReindexRoundTripTrue :
  Reindex.ExactCarrierReindex.decode Reindex.boolSwapReindex
    (Reindex.ExactCarrierReindex.encode Reindex.boolSwapReindex true) ≡ true
boolReindexRoundTripTrue = refl
