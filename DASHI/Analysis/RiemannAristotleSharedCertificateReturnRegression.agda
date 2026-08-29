module DASHI.Analysis.RiemannAristotleSharedCertificateReturnRegression where

open import DASHI.Core.Prelude

import DASHI.Analysis.RiemannAristotleSharedCertificateReturnExact as Return
import DASHI.Analysis.RiemannAristotleSharedWindowCertificateExact as Shared
import DASHI.Analysis.CertifiedFiniteCarrierReindexExact as Reindex

sharedEvidenceOnce :
  Return.SharedCertificatePatternReturn.sharedEvidenceConstructedOnce
    Return.canonicalSharedCertificatePatternReturn ≡ true
sharedEvidenceOnce = refl

certifiedCarrierEstimatesPreferred :
  Return.SharedCertificatePatternReturn.estimatesAttachToCertifiedCarrier
    Return.canonicalSharedCertificatePatternReturn ≡ true
certifiedCarrierEstimatesPreferred = refl

crossDraftCodeNotImported :
  Return.SharedCertificatePatternReturn.crossDraftCodeImported
    Return.canonicalSharedCertificatePatternReturn ≡ false
crossDraftCodeNotImported = refl

endpointComparisonStillNotFabricated :
  Shared.SharedWindowBudgetCutset.endpointComparisonDerivedHere
    Shared.canonicalSharedWindowBudgetCutset ≡ false
endpointComparisonStillNotFabricated = refl

concreteMultiZeroCarrierStillOpen :
  Reindex.CertifiedCarrierReindexBoundary.multiZeroConcreteCarrierConstructedHere
    Reindex.canonicalCertifiedCarrierReindexBoundary ≡ false
concreteMultiZeroCarrierStillOpen = refl
