module DASHI.Physics.Closure.W5PDFCarrierExternalConfirmedGap where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Float using (Float)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Unit using (⊤; tt)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.PDFCarrierLogRatioDiagnostic as PDFLog
import DASHI.Physics.Closure.W5PDFCarrierExternalIntakeRequest as Intake

------------------------------------------------------------------------
-- W5 PDF-carrier confirmed external gap.
--
-- This is a non-promoting certificate for the latest W5/PDF carrier result:
-- the DGLAP/LO plus carrier-correction route remains insufficient for the
-- required t45 correction.  The certificate therefore preserves the external
-- CT18/MSHT/LHAPDF intake requirement.  It does not claim that any external
-- provider table was fetched, processed, or locally verified.

data W5PDFCarrierExternalGapStatus : Set where
  dglapLOCarrierCorrectionStillInsufficient :
    W5PDFCarrierExternalGapStatus

data W5PDFCarrierExternalProviderRequirement : Set where
  ct18MSHTLHAPDFInputStillRequired :
    W5PDFCarrierExternalProviderRequirement

data W5PDFCarrierExternalVerificationStatus : Set where
  noLocalExternalPDFVerificationPresent :
    W5PDFCarrierExternalVerificationStatus

record W5PDFCarrierExternalConfirmedGap : Set where
  field
    gapStatus :
      W5PDFCarrierExternalGapStatus

    intakeRequest :
      Intake.W5PDFCarrierExternalIntakeRequest

    nearestPathDiagnostic :
      PDFLog.PDFCarrierLogRatioDiagnostic

    requiredT45Correction :
      Float

    localAttemptRoute :
      List String

    localAttemptClosesRequiredT45Correction :
      Bool

    remainingProviderRequirement :
      W5PDFCarrierExternalProviderRequirement

    externalVerificationStatus :
      W5PDFCarrierExternalVerificationStatus

    requiredExternalInputs :
      List String

    confirmedGapNotes :
      List String

    noNetworkFetchPerformed :
      Bool

    noExternalProviderVerificationClaimed :
      ⊤

    noPDFCarrierConstructed :
      ⊤

    noPartonLuminosityAuthorityFabricated :
      ⊤

    noGRQFTClosurePromotionConstructed :
      ⊤

canonicalW5PDFCarrierExternalConfirmedGap :
  W5PDFCarrierExternalConfirmedGap
canonicalW5PDFCarrierExternalConfirmedGap =
  record
    { gapStatus =
        dglapLOCarrierCorrectionStillInsufficient
    ; intakeRequest =
        Intake.canonicalW5PDFCarrierExternalIntakeRequest
    ; nearestPathDiagnostic =
        PDFLog.canonicalPDFCarrierLogRatioDiagnostic
    ; requiredT45Correction =
        0.8804486068
    ; localAttemptRoute =
        "DGLAP/LO plus carrier-correction route was considered only as a local diagnostic"
        ∷ "the local route does not supply a CT18, MSHT, or LHAPDF-compatible parton-luminosity table"
        ∷ "the local route does not discharge the required t45 correction 0.8804486068"
        ∷ []
    ; localAttemptClosesRequiredT45Correction =
        false
    ; remainingProviderRequirement =
        ct18MSHTLHAPDFInputStillRequired
    ; externalVerificationStatus =
        noLocalExternalPDFVerificationPresent
    ; requiredExternalInputs =
        "CT18 table and version, or"
        ∷ "MSHT table and version, or"
        ∷ "LHAPDF-compatible provider payload with accepted parton-luminosity route"
        ∷ "provider-side correction statement for CMS-SMP-20-003 t45 targeting 0.8804486068"
        ∷ []
    ; confirmedGapNotes =
        "DGLAP/LO plus carrier correction is not encoded as a successful PDF-carrier derivation"
        ∷ "the exact W5 status remains awaiting external PDF carrier intake"
        ∷ "no external CT18/MSHT/LHAPDF verification artifact is present in this module"
        ∷ []
    ; noNetworkFetchPerformed =
        true
    ; noExternalProviderVerificationClaimed =
        tt
    ; noPDFCarrierConstructed =
        tt
    ; noPartonLuminosityAuthorityFabricated =
        tt
    ; noGRQFTClosurePromotionConstructed =
        tt
    }

canonicalW5PDFCarrierExternalConfirmedGapStatus :
  W5PDFCarrierExternalConfirmedGap.gapStatus
    canonicalW5PDFCarrierExternalConfirmedGap
    ≡
  dglapLOCarrierCorrectionStillInsufficient
canonicalW5PDFCarrierExternalConfirmedGapStatus = refl

canonicalW5PDFCarrierExternalInputStillRequired :
  W5PDFCarrierExternalConfirmedGap.remainingProviderRequirement
    canonicalW5PDFCarrierExternalConfirmedGap
    ≡
  ct18MSHTLHAPDFInputStillRequired
canonicalW5PDFCarrierExternalInputStillRequired = refl

canonicalW5PDFCarrierExternalIntakeStillBlocked :
  Intake.W5PDFCarrierExternalIntakeRequest.intakeStatus
    (W5PDFCarrierExternalConfirmedGap.intakeRequest
      canonicalW5PDFCarrierExternalConfirmedGap)
    ≡
  Intake.awaitingExternalPDFCarrierIntake
canonicalW5PDFCarrierExternalIntakeStillBlocked = refl
