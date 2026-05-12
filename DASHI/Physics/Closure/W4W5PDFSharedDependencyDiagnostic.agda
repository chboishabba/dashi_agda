module DASHI.Physics.Closure.W4W5PDFSharedDependencyDiagnostic where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Float using (Float)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Unit using (⊤; tt)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Primitive using (Setω)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.W4ZPeakCalibrationAnchorReceipt as W4ZPeak
import DASHI.Physics.Closure.W4W5AcceptedDYLuminosityConventionDiagnostic as DYConvention
import DASHI.Physics.Closure.W5CT18ExternalIntakeReceipt as W5CT18
import DASHI.Physics.Closure.W5PDFCarrierExternalConfirmedGap as W5Gap

------------------------------------------------------------------------
-- W4/W5 shared external PDF dependency diagnostic.
--
-- This is a non-promoting Maxwell-Faraday lane receipt.  It records that the
-- current W4 dirty Z-peak shape adequacy blocker and the current W5 t45
-- correction blocker have the same upstream missing ingredient: an accepted
-- CT18/MSHT/LHAPDF-compatible parton-luminosity/PDF intake packet.
--
-- The receipt does not claim W4 closes, does not claim a successful Z-peak
-- anchor, does not construct an external PDF carrier, and does not promote W5.

data W4W5PDFSharedDependencyStatus : Set where
  w4ShapeAndW5T45ShareExternalPDFDependency :
    W4W5PDFSharedDependencyStatus

data W4W5PDFSharedFirstMissing : Set where
  missingSharedAcceptedDYLuminosityConventionAuthority :
    W4W5PDFSharedFirstMissing
  missingSharedCT18MSHTLHAPDFPartonLuminosityIntake :
    W4W5PDFSharedFirstMissing

record W4W5PDFSharedDependencyDiagnostic : Setω where
  field
    status :
      W4W5PDFSharedDependencyStatus

    w4ZPeakAnchorDiagnostic :
      W4ZPeak.W4ZPeakCalibrationAnchorMissingArtifactDiagnostic

    w5CT18IntakeReceipt :
      W5CT18.W5CT18ExternalIntakeReceipt

    w5ConfirmedExternalGap :
      W5Gap.W5PDFCarrierExternalConfirmedGap

    dyLuminosityConventionDiagnostic :
      DYConvention.W4W5AcceptedDYLuminosityConventionDiagnostic

    authorityFirstMissing :
      DYConvention.W4W5DYLuminosityFirstMissing

    firstMissing :
      W4W5PDFSharedFirstMissing

    sharedEquivalentFirstMissingName :
      String

    w4FirstMissingLabel :
      String

    w5FirstMissingLabel :
      String

    sharedMissingLabel :
      String

    exactFirstMissingStatus :
      String

    w4CurrentShapeFitChi2PerDof :
      String

    w4CurrentShapeFitDigest :
      String

    w5RequiredT45Correction :
      Float

    w5RequiredT45CorrectionDecimal :
      String

    acceptedProviderFamilies :
      List String

    sharedProviderPayload :
      List String

    packetPrecisionFields :
      List String

    localPDFIntakeAudit :
      List String

    rapidityIntegratedConventionAudit :
      List String

    acceptedConventionGate :
      List String

    acceptedAuthorityReceiptSurface :
      List String

    sharedMissingAuthorityFields :
      List DYConvention.W4W5DYLuminosityAuthorityField

    providerReadyMergeContract :
      List String

    dependencyRationale :
      List String

    nextAdmissibleAction :
      String

    noW4AnchorClosure :
      ⊤

    noW4Promotion :
      ⊤

    noW5T45Promotion :
      ⊤

    noExternalPDFCarrierConstructed :
      ⊤

canonicalW4W5PDFSharedDependencyDiagnostic :
  W4W5PDFSharedDependencyDiagnostic
canonicalW4W5PDFSharedDependencyDiagnostic =
  record
    { status =
        w4ShapeAndW5T45ShareExternalPDFDependency
    ; w4ZPeakAnchorDiagnostic =
        W4ZPeak.canonicalW4ZPeakCalibrationAnchorMissingArtifactDiagnostic
    ; w5CT18IntakeReceipt =
        W5CT18.canonicalW5CT18ExternalIntakeReceipt
    ; w5ConfirmedExternalGap =
        W5Gap.canonicalW5PDFCarrierExternalConfirmedGap
    ; dyLuminosityConventionDiagnostic =
        DYConvention.canonicalW4W5AcceptedDYLuminosityConventionDiagnostic
    ; authorityFirstMissing =
        DYConvention.missingAcceptedDYLuminosityConventionAuthority
    ; firstMissing =
        missingSharedAcceptedDYLuminosityConventionAuthority
    ; sharedEquivalentFirstMissingName =
        "missingSharedAcceptedDYLuminosityConventionAuthority"
    ; w4FirstMissingLabel =
        "W4 first missing remains missingDirtyZPeakShapeAdequacy; current local shape fit chi2/dof is 298.8462841768543"
    ; w5FirstMissingLabel =
        "W5 first missing remains CT18/MSHT/LHAPDF packet fields and computed t45 correction"
    ; sharedMissingLabel =
        "missingAcceptedDYLuminosityConventionAuthority, surfaced through the shared CT18/MSHT/LHAPDF-compatible parton-luminosity intake"
    ; exactFirstMissingStatus =
        "first missing: accepted W4/W5 Drell-Yan luminosity and mass-bin integration convention authority/provenance; local CT18NLO rapidity-window packet is candidate-only and rejected against the W5 target"
    ; w4CurrentShapeFitChi2PerDof =
        "298.8462841768543"
    ; w4CurrentShapeFitDigest =
        "36191efc92cb3c9b1641c9206171a307c4796369a4acd1485bf87d1051662b8b"
    ; w5RequiredT45Correction =
        0.8804486068
    ; w5RequiredT45CorrectionDecimal =
        "0.8804486068"
    ; acceptedProviderFamilies =
        "CT18"
        ∷ "MSHT"
        ∷ "NNPDF"
        ∷ "LHAPDF-compatible equivalent"
        ∷ []
    ; sharedProviderPayload =
        "PDF set identifier and version"
        ∷ "LHAPDF grid/checksum or equivalent provider table checksum"
        ∷ "parton-luminosity route for CMS-SMP-20-003 below-Z, Z-peak, and t45 windows"
        ∷ "x and Q2 convention for the 50-76, 76-106, and 106-170 GeV mass windows"
        ∷ "flavour/channel convention for the Drell-Yan q qbar luminosity ratio"
        ∷ "computed W5 t45 correction targeting 0.8804486068"
        ∷ "W4 Z-peak shape adequacy statement under the same PDF/parton-luminosity conventions"
        ∷ "authority/provenance receipt for the external PDF table or equivalent mass-kernel route"
        ∷ []
    ; packetPrecisionFields =
        "PDF set/version: exact family, member, error-set prescription, perturbative order, alpha_s value, and release label"
        ∷ "grid checksum: LHAPDF .dat/.info checksum or provider-table digest for every grid used by W4 and W5"
        ∷ "parton-luminosity convention: initial-state flavours, q qbar symmetrisation, collider energy, normalization, and bin integration rule"
        ∷ "x/Q2 convention: mapping from each CMS-SMP-20-003 mass window to x1, x2, Q2 or Q, including bin-centre versus integrated treatment"
        ∷ "W4 extraction: produce the dirty Z-peak 76-106 GeV shape prediction for the local t21/t22 covariance path and report chi2/dof against 298.8462841768543 baseline"
        ∷ "W5 extraction: produce the 106-170 over 76-106 t45 correction factor and compare with target 0.8804486068"
        ∷ "tolerance: state numerical tolerance, covariance treatment, PDF uncertainty treatment, and pass/fail criterion for both W4 shape and W5 t45"
        ∷ "provenance: record provider, command/API, input filenames, checksums, timestamp, and no-manual-overfit attestation"
        ∷ []
    ; localPDFIntakeAudit =
        "local HEPData t21/t22 and t45/t46 CSV artifacts are present under scripts/data/hepdata"
        ∷ "CT18NLO archive is present at scripts/data/pdf/CT18NLO.tar.gz; SHA-256 c9127231e77e97cbec79cb5839203ab00f8db77237a061b61f9420f2b7b9c213"
        ∷ "CT18NLO central grid is present at scripts/data/pdf/CT18NLO/CT18NLO_0000.dat; SHA-256 375db856d2f8c7087a626c92ebf228d3f080e5de83175519778ffaf6e72e5410"
        ∷ "scripts/extract_ct18_pdf_packet.py parsed the lhagrid1 table and wrote scripts/data/pdf/ct18_dashi_pdf_packet.json"
        ∷ "Euler 2026-05-13 reran the CT18 equivalent-table candidate at logs/research/w4w5_pdf_ct18_candidate_run_20260513.json; SHA-256 7b4e5e815c3e65619cd9591734eb00e7c80be0402c6d06c3c8d33d1c8da6609f"
        ∷ "Euler 2026-05-13 emitted logs/research/w4w5_pdf_lhapdf_intake_obstruction_20260513.json; SHA-256 a67318e71b4c18fde71597874f93aa28ab020557f230dd3843f807e40545b88d"
        ∷ "local fixed-x u-quark xfxQ extraction gives W5 correction 1.0506681065158017 with gap 0.17021949971580164 from target 0.8804486068"
        ∷ "prediction baseline inspected at DASHI.Physics.Prediction.sigma_dashi:predict_ratio_106_170_over_76_106, which computes sigma_DASHI(106-170, phi bin) / sigma_DASHI(76-106, phi bin)"
        ∷ "python importlib.util.find_spec(\"lhapdf\") returned absent; lhapdf-config and lhapdf executables were not found on PATH; no local MSHT20 grid was found by the 2026-05-13 preflight"
        ∷ []
    ; rapidityIntegratedConventionAudit =
        "scripts/extract_ct18_pdf_packet.py now also evaluates a rapidity-window Drell-Yan light-quark luminosity convention over the local CT18NLO grid"
        ∷ "convention: sqrt_s = 13000 GeV, eta_cut = 2.4, n_x = 200, n_m = 80, flavours u/d/s with charge weights 4/9, 1/9, 1/9"
        ∷ "center luminosities: t43 = 179275.14868433212, t45 = 24220.800992111075, ratio = 0.13510406305538247"
        ∷ "mass-window luminosities: t43 = 4694301.66970352, z_peak = 2092088.6841268337, t45 = 1572004.6396784543"
        ∷ "window ratios: z_peak/t43 = 0.4456655816623231, t45/z_peak = 0.7514043986785174, t45/t43 = 0.3348750784006896"
        ∷ "z-peak denominator probe gives t45/z_peak = 0.7514043986785174; abs gap from target 0.8804486068 is 0.12904420812148265"
        ∷ "t43 denominator hypothesis was tested directly: t45/t43 = 0.3348750784006896; abs gap from target 0.8804486068 is 0.5455735283993104"
        ∷ "therefore changing only the denominator to t43 does not close W4/W5 under the current rapidity-window CT18 convention"
        ∷ "the CT18 packet now records formula, bin integration, scale choice, flavour sum, PDF member, checksums, and citation fields, but marks the convention candidate-not-accepted"
        ∷ "the first missing item remains an accepted parton-luminosity/bin-integration convention that maps CT18NLO to the DASHI t45 correction surface"
        ∷ []
    ; acceptedConventionGate =
        "do not merge this diagnostic into W4 closure without accepted convention provenance and a W4 dirty Z-peak shape adequacy pass under that convention"
        ∷ "do not merge this diagnostic into W5 closure without accepted convention provenance and a t45 correction/tolerance pass under that convention"
        ∷ "the present local CT18NLO packet is admissible as provenance input only, not as the accepting authority"
        ∷ "the rejected ratios remain part of the audit surface: fixed-x = 1.0506681065158017, t45/z_peak = 0.7514043986785174, t45/t43 = 0.3348750784006896"
        ∷ []
    ; acceptedAuthorityReceiptSurface =
        "first missing name: missingAcceptedDYLuminosityConventionAuthority"
        ∷ "PDF set: authority must accept CT18NLO or replacement PDF family/version"
        ∷ "LHAPDF id: authority must accept id 14400 or replacement id"
        ∷ "grid checksum: authority must accept the grid/table checksum used by W4 and W5"
        ∷ "factorization scale convention: authority must accept Q = M or an explicit Q2 alternative"
        ∷ "rapidity window: authority must accept eta_cut = 2.4 or an explicit replacement"
        ∷ "mass-bin integration rule: authority must accept the 50-76, 76-106, and 106-170 GeV integration rule"
        ∷ "flavour-weight rule: authority must accept charge weights, q qbar symmetrisation, and heavy-flavour handling"
        ∷ "source DOI: authority must provide the DOI or equivalent provider citation"
        ∷ "external authority/provenance: authority must name provider, command/API, inputs, checksums, timestamp, and acceptance statement"
        ∷ []
    ; sharedMissingAuthorityFields =
        DYConvention.W4W5AcceptedDYLuminosityConventionDiagnostic.missingAuthorityFields
          DYConvention.canonicalW4W5AcceptedDYLuminosityConventionDiagnostic
    ; providerReadyMergeContract =
        "shared receipt must use the accepted-DY authority as the first missing item, not a W4 or W5 closure claim"
        ∷ "shared receipt must route W4 shape adequacy and W5 t45 correction through the same accepted convention authority"
        ∷ "shared receipt may cite local CT18NLO ratios only as candidate/falsified probes"
        ∷ "shared receipt must keep missingSharedCT18MSHTLHAPDFPartonLuminosityIntake as a broader dependency label, not the exact authority blocker"
        ∷ []
    ; dependencyRationale =
        "The W4 dirty Z-peak data and covariance are local and parsed, but the current carrier-only shape fit is inadequate"
        ∷ "The W5 t45 route already records that local DGLAP/carrier diagnostics do not provide an accepted PDF carrier"
        ∷ "Both blockers require an accepted parton-luminosity/PDF intake before their downstream comparison surfaces can be evaluated"
        ∷ "This receipt merges the provider-facing dependency; it does not merge W4 and W5 promotions"
        ∷ []
    ; nextAdmissibleAction =
        "supply the accepted parton-luminosity/bin-integration convention over the local CT18NLO grid, or an equivalent provider-authority packet, then rerun W4 Z-peak shape adequacy and W5 t45 correction checks"
    ; noW4AnchorClosure =
        tt
    ; noW4Promotion =
        tt
    ; noW5T45Promotion =
        tt
    ; noExternalPDFCarrierConstructed =
        tt
    }

canonicalW4W5SharedFirstMissing :
  W4W5PDFSharedDependencyDiagnostic.firstMissing
    canonicalW4W5PDFSharedDependencyDiagnostic
    ≡
  missingSharedAcceptedDYLuminosityConventionAuthority
canonicalW4W5SharedFirstMissing =
  refl

canonicalW4W5SharedAuthorityFirstMissing :
  W4W5PDFSharedDependencyDiagnostic.authorityFirstMissing
    canonicalW4W5PDFSharedDependencyDiagnostic
    ≡
  DYConvention.missingAcceptedDYLuminosityConventionAuthority
canonicalW4W5SharedAuthorityFirstMissing =
  refl

canonicalW4W5SharedDependencyDoesNotCloseW4 :
  W4W5PDFSharedDependencyDiagnostic.noW4Promotion
    canonicalW4W5PDFSharedDependencyDiagnostic
    ≡ tt
canonicalW4W5SharedDependencyDoesNotCloseW4 =
  refl

canonicalW4W5SharedDependencyDoesNotPromoteW5 :
  W4W5PDFSharedDependencyDiagnostic.noW5T45Promotion
    canonicalW4W5PDFSharedDependencyDiagnostic
    ≡ tt
canonicalW4W5SharedDependencyDoesNotPromoteW5 =
  refl
