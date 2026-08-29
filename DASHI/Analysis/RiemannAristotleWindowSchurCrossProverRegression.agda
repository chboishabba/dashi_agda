module DASHI.Analysis.RiemannAristotleWindowSchurCrossProverRegression where

open import DASHI.Core.Prelude

import DASHI.Analysis.ResidualBudgetMarginCompilerExact as Budget
import DASHI.Analysis.RiemannAristotleWindowSchurCrossProverSyncExact as Sync

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
