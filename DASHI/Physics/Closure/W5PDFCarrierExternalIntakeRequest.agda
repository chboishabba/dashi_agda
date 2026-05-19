module DASHI.Physics.Closure.W5PDFCarrierExternalIntakeRequest where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Float using (Float)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Unit using (⊤; tt)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.PDFCarrierLogRatioDiagnostic as PDFLog
import DASHI.Physics.Closure.W4W5AcceptedDYLuminosityConventionDiagnostic as DYConvention

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

data LHAPDF6ExternalIntakeContractField : Set where
  lhapdf6RuntimeOrEquivalentTableReader :
    LHAPDF6ExternalIntakeContractField
  ct18nloSetID14400OrAcceptedReplacement :
    LHAPDF6ExternalIntakeContractField
  msht20SetIDOrAcceptedReplacement :
    LHAPDF6ExternalIntakeContractField
  centralMemberAndErrorPrescription :
    LHAPDF6ExternalIntakeContractField
  infoAndMemberGridChecksums :
    LHAPDF6ExternalIntakeContractField
  xfxQOrXFXQ2EvaluationConvention :
    LHAPDF6ExternalIntakeContractField
  interpolationExtrapolationPolicy :
    LHAPDF6ExternalIntakeContractField
  alphaSAndOrderConvention :
    LHAPDF6ExternalIntakeContractField
  dyPartonLuminosityFormula :
    LHAPDF6ExternalIntakeContractField
  massWindowBinIntegrationConvention :
    LHAPDF6ExternalIntakeContractField
  rapidityOrEtaAcceptanceConvention :
    LHAPDF6ExternalIntakeContractField
  flavourWeightsAndHeavyFlavourPolicy :
    LHAPDF6ExternalIntakeContractField
  w4W5RunnerConversionLaw :
    LHAPDF6ExternalIntakeContractField
  provenanceAndNoManualOverfitAttestation :
    LHAPDF6ExternalIntakeContractField

canonicalLHAPDF6ExternalIntakeContractFields :
  List LHAPDF6ExternalIntakeContractField
canonicalLHAPDF6ExternalIntakeContractFields =
  lhapdf6RuntimeOrEquivalentTableReader
  ∷ ct18nloSetID14400OrAcceptedReplacement
  ∷ msht20SetIDOrAcceptedReplacement
  ∷ centralMemberAndErrorPrescription
  ∷ infoAndMemberGridChecksums
  ∷ xfxQOrXFXQ2EvaluationConvention
  ∷ interpolationExtrapolationPolicy
  ∷ alphaSAndOrderConvention
  ∷ dyPartonLuminosityFormula
  ∷ massWindowBinIntegrationConvention
  ∷ rapidityOrEtaAcceptanceConvention
  ∷ flavourWeightsAndHeavyFlavourPolicy
  ∷ w4W5RunnerConversionLaw
  ∷ provenanceAndNoManualOverfitAttestation
  ∷ []

record W5PDFCarrierExternalIntakeRequest : Set where
  field
    intakeStatus :
      W5PDFCarrierIntakeStatus

    localCacheStatus :
      W5PDFCarrierLocalCacheStatus

    nearestPathDiagnostic :
      PDFLog.PDFCarrierLogRatioDiagnostic

    authorityFirstMissing :
      DYConvention.W4W5DYLuminosityFirstMissing

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

    lhapdf6ExternalIntakeContract :
      List LHAPDF6ExternalIntakeContractField

    lhapdf6ExternalIntakeContractIsCanonical :
      lhapdf6ExternalIntakeContract
      ≡
      canonicalLHAPDF6ExternalIntakeContractFields

    lhapdf6ExternalIntakeContractLabels :
      List String

    extractionContract :
      List String

    acceptedConventionBlocker :
      List String

    acceptedAuthorityReceiptSurface :
      List String

    missingAuthorityFields :
      List DYConvention.W4W5DYLuminosityAuthorityField

    providerAuthorityContract :
      List String

    observedLocalCache :
      List String

    observedLocalTooling :
      List String

    localCT18GridParsed :
      Bool

    localCT18GridParsedIsTrue :
      localCT18GridParsed ≡ true

    localCT18DASHIProjectionBinding :
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
    ; authorityFirstMissing =
        DYConvention.missingAcceptedDYLuminosityConventionAuthority
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
        "PDF set identifier and version accepted by the convention authority"
        ∷ "LHAPDF id accepted by the convention authority, currently candidate id 14400 for CT18NLO"
        ∷ "grid checksum accepted by the convention authority for every .info/.dat or provider-table artifact"
        ∷ "parton-luminosity correction for the CMS-SMP-20-003 t45 window"
        ∷ "factorization scale convention used for the 50-76, 76-106, and 106-170 GeV mass windows"
        ∷ "rapidity-window convention used by the accepted Drell-Yan parton-luminosity route"
        ∷ "mass-bin integration rule for the 50-76, 76-106, and 106-170 GeV windows"
        ∷ "flavour-weight rule used to form the Drell-Yan parton-luminosity ratio"
        ∷ "computed correction factor targeting 0.8804486068"
        ∷ "source DOI for the PDF set and/or accepted luminosity convention"
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
    ; lhapdf6ExternalIntakeContract =
        canonicalLHAPDF6ExternalIntakeContractFields
    ; lhapdf6ExternalIntakeContractIsCanonical =
        refl
    ; lhapdf6ExternalIntakeContractLabels =
        "LHAPDF-6 runtime route or equivalent table reader with version recorded"
        ∷ "CT18NLO candidate: SetIndex/LHAPDF id 14400, accepted only if authority payload says so"
        ∷ "MSHT20 candidate: exact LHAPDF set id/version/member must be supplied by the payload if used"
        ∷ "central member and uncertainty/error-set prescription"
        ∷ ".info and every consumed member grid checksum"
        ∷ "xfxQ/xfxQ2 convention and whether the table stores x*f(x,Q)"
        ∷ "interpolation/extrapolation policy over x and Q"
        ∷ "alphaS, perturbative order, and flavour-scheme convention"
        ∷ "Drell-Yan q qbar luminosity formula and normalization"
        ∷ "50-76, 76-106, and 106-170 GeV mass-window bin integration"
        ∷ "rapidity/eta acceptance convention"
        ∷ "charge weights, symmetrisation, and heavy-flavour policy"
        ∷ "conversion law to W4 ell_i and W5 L43/L45 runner inputs"
        ∷ "provider provenance and no-manual-overfit attestation"
        ∷ []
    ; extractionContract =
        "compute the 106-170 over 76-106 Drell-Yan parton-luminosity correction for CMS-SMP-20-003 t45"
        ∷ "report numerator and denominator luminosity values before forming the correction factor"
        ∷ "report computed correction factor and residual relative to 0.8804486068"
        ∷ "do not promote W5 unless the packet satisfies the provider precision fields and the tolerance statement passes"
        ∷ []
    ; acceptedConventionBlocker =
        "missingAcceptedDYLuminosityConventionAuthority is the first missing item"
        ∷ "accepted DY luminosity convention authority is absent"
        ∷ "accepted mass-bin integration convention over the CMS-SMP-20-003 windows is absent"
        ∷ "accepted CT18NLO member/error-set and PDF uncertainty convention is absent"
        ∷ "accepted numeric tolerance/covariance treatment tying the local CT18 packet to W4/W5 is absent"
        ∷ []
    ; acceptedAuthorityReceiptSurface =
        "PDF set"
        ∷ "LHAPDF id"
        ∷ "grid checksum"
        ∷ "factorization scale convention"
        ∷ "rapidity window"
        ∷ "mass-bin integration rule"
        ∷ "flavour-weight rule"
        ∷ "source DOI"
        ∷ "external authority/provenance"
        ∷ []
    ; missingAuthorityFields =
        DYConvention.W4W5AcceptedDYLuminosityConventionDiagnostic.missingAuthorityFields
          DYConvention.canonicalW4W5AcceptedDYLuminosityConventionDiagnostic
    ; providerAuthorityContract =
        "external intake must provide authority for the DY luminosity convention before a PDF carrier can be constructed"
        ∷ "external intake must mark local CT18NLO probes as candidate-only or supersede them with an accepted authority receipt"
        ∷ "external intake must not infer W5 closure from the presence of CT18 files, checksums, or candidate ratios"
        ∷ "external intake must preserve first missing missingAcceptedDYLuminosityConventionAuthority until authority/provenance is accepted"
        ∷ []
    ; observedLocalCache =
        "scripts/data/hepdata has t43/t44, t45/t46, and t19/t20 HEPData tables"
        ∷ "scripts/data/outputs has t43/t45 projection JSON artifacts"
        ∷ "scripts/data/pdf/CT18NLO.tar.gz is present; SHA-256 c9127231e77e97cbec79cb5839203ab00f8db77237a061b61f9420f2b7b9c213"
        ∷ "scripts/data/pdf/CT18NLO/CT18NLO_0000.dat central grid is present; SHA-256 375db856d2f8c7087a626c92ebf228d3f080e5de83175519778ffaf6e72e5410"
        ∷ "scripts/data/pdf/ct18_dashi_pdf_packet.json records the local extraction"
        ∷ "logs/research/w4w5_pdf_ct18_candidate_run_20260513.json records the fresh Euler CT18 equivalent-table candidate run; SHA-256 7b4e5e815c3e65619cd9591734eb00e7c80be0402c6d06c3c8d33d1c8da6609f"
        ∷ "the packet identifies the repo t45 baseline as sigma_DASHI(106-170, phi bin) / sigma_DASHI(76-106, phi bin)"
        ∷ "the packet includes the z-peak denominator rapidity-window DY luminosity ratio t45/z_peak = 0.7514043986785174 with gap 0.12904420812148265 from target 0.8804486068"
        ∷ "the packet also records the t43 denominator hypothesis directly: t45/t43 window ratio 0.3348750784006896 with gap 0.5455735283993104"
        ∷ "the packet now records formula, bin integration, scale choice, flavour sum, CT18NLO info digest be60232d8e6c49982c82f5fa990fd5b0fd1050719944f31602bf27cdb16548b0, and required authority fields"
        ∷ "the packet status is candidate_local_ct18nlo_convention_not_accepted with first missing missingAcceptedDYLuminosityConventionAuthority"
        ∷ []
    ; observedLocalTooling =
        "2026-05-13 Euler preflight: python3 importlib.util.find_spec(\"lhapdf\") returned absent under /usr/bin/python3 3.14.4"
        ∷ "2026-05-13 Euler preflight: lhapdf-config was not found on PATH"
        ∷ "2026-05-13 Euler preflight: lhapdf executable was not found on PATH"
        ∷ "2026-05-13 Euler preflight: no local MSHT20 grid candidates were found under scripts/data/pdf, ~/.local/share/LHAPDF, /usr/local/share/LHAPDF, or /usr/share/LHAPDF"
        ∷ "logs/research/w4w5_pdf_lhapdf_intake_obstruction_20260513.json records this tool/provider obstruction; SHA-256 a67318e71b4c18fde71597874f93aa28ab020557f230dd3843f807e40545b88d"
        ∷ "repo-local scripts/extract_ct18_pdf_packet.py parsed the CT18NLO lhagrid1 central member without LHAPDF runtime bindings"
        ∷ []
    ; localCT18GridParsed =
        true
    ; localCT18GridParsedIsTrue =
        refl
    ; localCT18DASHIProjectionBinding =
        "parsed CT18 packet: scripts/data/pdf/ct18_dashi_pdf_packet.json"
        ∷ "candidate DY convention: rapidity-window light-quark luminosity, Q = dilepton mass, eta_cut = 2.4, n_x = 200, n_m = 80"
        ∷ "candidate windows: t43 50-76 GeV, z peak 76-106 GeV, t45 106-170 GeV"
        ∷ "candidate projection artifacts: scripts/data/outputs/t43_projection_v4.json and scripts/data/outputs/t45_projection_v4.json"
        ∷ "binding status: local candidate provenance only; accepted authority and runner conversion law remain missing"
        ∷ []
    ; exactExternalIntakeBlocker =
        "first missing: missingAcceptedDYLuminosityConventionAuthority; real LHAPDF runtime and MSHT20 grid are absent in the 2026-05-13 Euler preflight; local CT18NLO rapidity-window DY query is provenance-ready but candidate-not-accepted: t45/z_peak = 0.7514043986785174 and t45/t43 = 0.3348750784006896, neither matching target 0.8804486068"
    ; networkFetchPerformed =
        false
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

canonicalW5PDFCarrierExternalIntakeAuthorityFirstMissing :
  W5PDFCarrierExternalIntakeRequest.authorityFirstMissing
    canonicalW5PDFCarrierExternalIntakeRequest
    ≡
  DYConvention.missingAcceptedDYLuminosityConventionAuthority
canonicalW5PDFCarrierExternalIntakeAuthorityFirstMissing =
  refl
