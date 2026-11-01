module DASHI.Analysis.RiemannAristotleWindowSchurCrossProverRegression where

open import DASHI.Core.Prelude

import DASHI.Analysis.ResidualBudgetMarginCompilerExact as Budget
import DASHI.Analysis.RiemannAristotleWindowSchurCrossProverSyncExact as Sync
import DASHI.Analysis.RiemannAristotleSharedWindowCertificateExact as Shared
import DASHI.Analysis.CertifiedFiniteCarrierReindexExact as Reindex
import DASHI.Analysis.RiemannAristotleTwoZeroThreeTaperReturnExact as TwoZero
import DASHI.Analysis.ExactSelectedEliminationFarTailCompilerExact as Far

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

normalizedEndpointTransportClosedInLean :
  Sync.AristotleAgdaSyncBoundary.normalizedEndpointTransportClosed
    Sync.canonicalAristotleAgdaSyncBoundary ≡ true
normalizedEndpointTransportClosedInLean = refl

twoZeroThreeTaperClosedInLean :
  Sync.AristotleAgdaSyncBoundary.inhabitedTwoZeroThreeTaperClosedInLean
    Sync.canonicalAristotleAgdaSyncBoundary ≡ true
twoZeroThreeTaperClosedInLean = refl

selectedTwoZeroDebtRetired :
  Sync.AristotleAgdaSyncBoundary.selectedTwoZeroResidualDebtRequired
    Sync.canonicalAristotleAgdaSyncBoundary ≡ false
selectedTwoZeroDebtRetired = refl

projectedFarTailStillOpen :
  Sync.AristotleAgdaSyncBoundary.projectedFarTailBudgetClosed
    Sync.canonicalAristotleAgdaSyncBoundary ≡ false
projectedFarTailStillOpen = refl

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

oneSymbolicEndpointComparisonRetired :
  Shared.SharedWindowBudgetCutset.oneSymbolicBudgetComparisonRemains
    Shared.canonicalSharedWindowBudgetCutset ≡ false
oneSymbolicEndpointComparisonRetired = refl

endpointComparisonClosedInLean :
  Shared.SharedWindowBudgetCutset.endpointComparisonClosedInLean
    Shared.canonicalSharedWindowBudgetCutset ≡ true
endpointComparisonClosedInLean = refl

endpointComparisonNotReprovedInAgda :
  Shared.SharedWindowBudgetCutset.endpointComparisonDerivedHere
    Shared.canonicalSharedWindowBudgetCutset ≡ false
endpointComparisonNotReprovedInAgda = refl

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

leanTwoZeroExactEliminationOwned :
  TwoZero.TwoZeroThreeTaperReturn.twoSelectedNuisancesEliminatedExactly
    TwoZero.canonicalTwoZeroThreeTaperReturn ≡ true
leanTwoZeroExactEliminationOwned = refl

localSelectedResidualDebtIsZero :
  TwoZero.TwoZeroFarTailFrontier.localSelectedResidualDebt
    TwoZero.canonicalTwoZeroFarTailFrontier ≡ false
localSelectedResidualDebtIsZero = refl

farTailEstimateNotProducedByCompiler :
  Far.ExactSelectedFarTailBoundary.farTailEstimateProducedByCompiler
    Far.canonicalExactSelectedFarTailBoundary ≡ false
farTailEstimateNotProducedByCompiler = refl
