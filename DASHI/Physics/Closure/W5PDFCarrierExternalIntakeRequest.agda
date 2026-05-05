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
  localCT18NLOGridParsedButConventionMismatch :
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

    providerPacketPrecision :
      List String

    extractionContract :
      List String

    observedLocalCache :
      List String

    observedLocalTooling :
      List String

    exactExternalIntakeBlocker :
      String

    networkFetchPerformed :
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
        localCT18NLOGridParsedButConventionMismatch
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
        ∷ "x and Q2 convention used for both 106-170 and 76-106 GeV mass windows"
        ∷ "flavour/channel convention used to form the Drell-Yan parton-luminosity ratio"
        ∷ "computed correction factor targeting 0.8804486068"
        ∷ "tolerance statement comparing the computed correction against 0.8804486068"
        ∷ "authority/provenance receipt for the PDF table or equivalent mass-kernel route"
        ∷ []
    ; providerPacketPrecision =
        "PDF set/version must include family, member, order, alpha_s, release label, and uncertainty prescription"
        ∷ "grid checksum must identify the LHAPDF .info/.dat files or equivalent provider table used for every evaluated point"
        ∷ "parton-luminosity convention must state q qbar symmetrisation, flavour sum, collider energy, normalization, and bin integration rule"
        ∷ "x/Q2 convention must state whether Q or Q2 is used and how the 106-170 and 76-106 GeV windows map to evaluated points"
        ∷ "tolerance must state numeric acceptance against 0.8804486068 and how PDF/covariance uncertainty enters the comparison"
        ∷ "provenance must include provider, API/command, input filenames, checksums, timestamp, and no-manual-overfit attestation"
        ∷ []
    ; extractionContract =
        "compute the 106-170 over 76-106 Drell-Yan parton-luminosity correction for CMS-SMP-20-003 t45"
        ∷ "report numerator and denominator luminosity values before forming the correction factor"
        ∷ "report computed correction factor and residual relative to 0.8804486068"
        ∷ "do not promote W5 unless the packet satisfies the provider precision fields and the tolerance statement passes"
        ∷ []
    ; observedLocalCache =
        "scripts/data/hepdata has t43/t44, t45/t46, and t19/t20 HEPData tables"
        ∷ "scripts/data/outputs has t43/t45 projection JSON artifacts"
        ∷ "scripts/data/pdf/CT18NLO.tar.gz is present; SHA-256 c9127231e77e97cbec79cb5839203ab00f8db77237a061b61f9420f2b7b9c213"
        ∷ "scripts/data/pdf/CT18NLO/CT18NLO_0000.dat central grid is present; SHA-256 375db856d2f8c7087a626c92ebf228d3f080e5de83175519778ffaf6e72e5410"
        ∷ "scripts/data/pdf/ct18_dashi_pdf_packet.json records the local extraction"
        ∷ "the packet identifies the repo t45 baseline as sigma_DASHI(106-170, phi bin) / sigma_DASHI(76-106, phi bin)"
        ∷ "the packet includes the matching rapidity-window DY luminosity ratio t45/z_peak = 0.7514043986785174 with gap 0.12904420812148265 from target 0.8804486068"
        ∷ "the packet also records the older non-matching t45/t43 window ratio 0.3348750784006896"
        ∷ []
    ; observedLocalTooling =
        "python3 importlib.util.find_spec(\"lhapdf\") returned absent; pip has no lhapdf wheel for this environment"
        ∷ "lhapdf-config was not found on PATH"
        ∷ "lhapdf executable was not found on PATH"
        ∷ "repo-local scripts/extract_ct18_pdf_packet.py parsed the CT18NLO lhagrid1 central member without LHAPDF runtime bindings"
        ∷ []
    ; exactExternalIntakeBlocker =
        "matching local CT18NLO rapidity-window DY query for sigma_DASHI(106-170)/sigma_DASHI(76-106) gives t45/z_peak = 0.7514043986785174, not target 0.8804486068; missing item is an accepted parton-luminosity/bin-integration convention and authority/provenance route"
    ; networkFetchPerformed =
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
