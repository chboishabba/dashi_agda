module DASHI.Planning.ConsentReparationPNFValidation where

open import DASHI.Core.Prelude
import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Planning.CollectiveTerritorialConsentExact as Consent
import DASHI.Planning.AuthoritySovereigntyNonDescentExact as Authority
import DASHI.Planning.NonSubstitutionalReparationExact as Repair
import DASHI.Planning.PlanningPNFClaimBoundaryExact as PNF

------------------------------------------------------------------------
-- Focused validation surface for the consent / authority / reparation / PNF
-- cross-pollination tranche.
------------------------------------------------------------------------

consultationStillNotConsent :
  Consent.CollectiveConsentEnvelope.stage Consent.consultationOnly ≡
  Consent.consentGiven → ⊥
consultationStillNotConsent = Consent.consultedIsNotConsentGiven

recognitionStillCannotConstituteEveryAuthority :
  INF.FactorsThrough Authority.recognitionObserver Authority.authorityObserver → ⊥
recognitionStillCannotConstituteEveryAuthority =
  Authority.stateRecognitionCannotConstituteEveryAuthority

compensationStillDoesNotRestoreAuthority :
  Repair.ReparativeBundle.status Repair.compensationOnly Repair.authorityRestorationAxis ≡
  Repair.repaired → ⊥
compensationStillDoesNotRestoreAuthority =
  Repair.compensationDoesNotRestoreAuthority

planningDoesNotHandAssignPNFResiduals :
  PNF.PlanningClaimBoundary.analystMayHandAssignResidual
    PNF.canonicalPlanningClaimBoundary ≡ false
planningDoesNotHandAssignPNFResiduals = refl
