module DASHI.Physics.Closure.W5PDFCarrierExternalIntakeRequest where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Float using (Float)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Unit using (⊤; tt)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.PDFCarrierLogRatioDiagnostic as PDFLog

------------------------------------------------------------------------
-- W5 external PDF-carrier intake request.
--
-- The local W5 diagnostic has ruled out a repo-internal derivation of the
-- t45 neutral-current correction.  This module records the exact external
-- intake blocker without fetching network data and without constructing a PDF
-- carrier, parton-luminosity authority, or GR/QFT promotion receipt.

data W5PDFCarrierLocalCacheStatus : Set where
  noLocalCT18MSHTNNPDFLHAPDFTablesFound :
    W5PDFCarrierLocalCacheStatus
  localPDFCarrierTablesPresentButNotProcessedHere :
    W5PDFCarrierLocalCacheStatus

data W5PDFCarrierIntakeStatus : Set where
  awaitingExternalPDFCarrierIntake :
    W5PDFCarrierIntakeStatus

record W5PDFCarrierExternalIntakeRequest : Set where
  field
    intakeStatus :
      W5PDFCarrierIntakeStatus

    localCacheStatus :
      W5PDFCarrierLocalCacheStatus

    nearestPathDiagnostic :
      PDFLog.PDFCarrierLogRatioDiagnostic

    requiredT45Correction :
      Float

    correctionNumerator :
      String

    correctionDenominator :
      String

    toleranceTarget :
      String

    acceptableProviderFamilies :
      List String

    requiredProviderPayload :
      List String

    observedLocalCache :
      List String

    exactExternalIntakeBlocker :
      String

    noNetworkFetchPerformed :
      Bool

    noPDFCarrierConstructed :
      ⊤

    noPartonLuminosityAuthorityFabricated :
      ⊤

    noGRQFTClosurePromotionConstructed :
      ⊤

canonicalW5PDFCarrierExternalIntakeRequest :
  W5PDFCarrierExternalIntakeRequest
canonicalW5PDFCarrierExternalIntakeRequest =
  record
    { intakeStatus =
        awaitingExternalPDFCarrierIntake
    ; localCacheStatus =
        noLocalCT18MSHTNNPDFLHAPDFTablesFound
    ; nearestPathDiagnostic =
        PDFLog.canonicalPDFCarrierLogRatioDiagnostic
    ; requiredT45Correction =
        0.8804486068
    ; correctionNumerator =
        "observed t45 mean = 0.026288"
    ; correctionDenominator =
        "current neutral-current t45 mean = 0.0298575065"
    ; toleranceTarget =
        "provider correction must account for 0.026288 / 0.0298575065 = 0.8804486068 within the W5 PDF-carrier tolerance"
    ; acceptableProviderFamilies =
        "CT18"
        ∷ "MSHT"
        ∷ "NNPDF"
        ∷ "LHAPDF-compatible table carrying an accepted parton-luminosity route"
        ∷ []
    ; requiredProviderPayload =
        "local or external table identifier and version"
        ∷ "parton-luminosity correction for the CMS-SMP-20-003 t45 window"
        ∷ "x and Q2 convention used for the 106-170 / 76-106 GeV ratio"
        ∷ "computed correction factor targeting 0.8804486068"
        ∷ "authority/provenance receipt for the PDF table or equivalent mass-kernel route"
        ∷ []
    ; observedLocalCache =
        "scripts/data/hepdata has t43/t44, t45/t46, and t19/t20 HEPData tables"
        ∷ "scripts/data/outputs has t43/t45 projection JSON artifacts"
        ∷ "no CT18, MSHT, NNPDF, or LHAPDF table was found in scripts/data during this lane"
        ∷ []
    ; exactExternalIntakeBlocker =
        "missing external PDF/parton-luminosity carrier for required t45 correction 0.8804486068"
    ; noNetworkFetchPerformed =
        true
    ; noPDFCarrierConstructed =
        tt
    ; noPartonLuminosityAuthorityFabricated =
        tt
    ; noGRQFTClosurePromotionConstructed =
        tt
    }

canonicalW5PDFCarrierExternalIntakeStillBlocked :
  W5PDFCarrierExternalIntakeRequest.intakeStatus
    canonicalW5PDFCarrierExternalIntakeRequest
    ≡
  awaitingExternalPDFCarrierIntake
canonicalW5PDFCarrierExternalIntakeStillBlocked = refl
