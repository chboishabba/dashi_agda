module DASHI.Planning.ConsentReparationPNFBoundary where

open import DASHI.Core.Prelude
import DASHI.Planning.CollectiveTerritorialConsentExact as Consent
import DASHI.Planning.AuthoritySovereigntyNonDescentExact as Authority
import DASHI.Planning.NonSubstitutionalReparationExact as Repair
import DASHI.Planning.PlanningPNFClaimBoundaryExact as Claim

------------------------------------------------------------------------
-- Aggregate boundary: none of the neighbouring representations is allowed to
-- substitute for the stronger relation it merely describes or partially
-- observes.
------------------------------------------------------------------------

record ConsentReparationPNFBoundary : Set where
  constructor consentReparationPNFBoundary
  field
    consultationIsConsent : Bool
    consultationIsConsentIsFalse : consultationIsConsent ≡ false
    stateRecognitionIsAuthorityOrigin : Bool
    stateRecognitionIsAuthorityOriginIsFalse :
      stateRecognitionIsAuthorityOrigin ≡ false
    compensationIsAuthorityRestoration : Bool
    compensationIsAuthorityRestorationIsFalse :
      compensationIsAuthorityRestoration ≡ false
    rhetoricIsFormalResidualWithoutReceipt : Bool
    rhetoricIsFormalResidualWithoutReceiptIsFalse :
      rhetoricIsFormalResidualWithoutReceipt ≡ false

canonicalConsentReparationPNFBoundary : ConsentReparationPNFBoundary
canonicalConsentReparationPNFBoundary =
  consentReparationPNFBoundary false refl false refl false refl false refl
