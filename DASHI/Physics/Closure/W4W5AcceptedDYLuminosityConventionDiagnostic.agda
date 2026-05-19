module DASHI.Physics.Closure.W4W5AcceptedDYLuminosityConventionDiagnostic where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Float using (Float)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Unit using (⊤; tt)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- W4/W5 accepted Drell-Yan luminosity convention diagnostic.
--
-- This is a provenance-ready negative diagnostic.  The local CT18NLO grid and
-- extractor now define a concrete Drell-Yan luminosity candidate, but this
-- module does not mark it as accepted and does not promote W4 or W5.  The
-- current first missing is the authority that accepts the luminosity
-- definition, bin integration, scale choice, flavour sum, PDF member/error
-- treatment, and tolerance as the convention for the W4/W5 comparison.

data W4W5DYLuminosityConventionStatus : Set where
  candidateLocalCT18NLOConventionNotAccepted :
    W4W5DYLuminosityConventionStatus

data W4W5DYLuminosityFirstMissing : Set where
  missingAcceptedDYLuminosityConventionAuthority :
    W4W5DYLuminosityFirstMissing

data W4W5DYLuminosityNumericStatus : Set where
  localCandidateDoesNotMatchW5Target :
    W4W5DYLuminosityNumericStatus

data W4W5DYLuminosityAuthorityReadiness : Set where
  acceptedAuthorityReceiptMissing :
    W4W5DYLuminosityAuthorityReadiness

data CT18DASHIProjectionConventionBindingStatus : Set where
  localCT18GridConventionBoundToProjectionArtifactsCandidateOnly :
    CT18DASHIProjectionConventionBindingStatus

data CT18DASHIProjectionConventionResidualField : Set where
  missingExternalAuthorityPayload :
    CT18DASHIProjectionConventionResidualField
  missingAcceptedCT18ConventionDecision :
    CT18DASHIProjectionConventionResidualField
  missingAcceptedDASHIProjectionConsumptionLaw :
    CT18DASHIProjectionConventionResidualField
  missingAcceptedW4PerBinLuminosityVector :
    CT18DASHIProjectionConventionResidualField
  missingAcceptedW5L43L45Luminosities :
    CT18DASHIProjectionConventionResidualField
  missingAcceptedEfficiencyAcceptanceModel :
    CT18DASHIProjectionConventionResidualField
  missingAcceptedSystematicBudget :
    CT18DASHIProjectionConventionResidualField
  missingAcceptedNormalizationPreservationLaw :
    CT18DASHIProjectionConventionResidualField
  missingAcceptedProviderToRunnerConversionLaw :
    CT18DASHIProjectionConventionResidualField
  missingAcceptedComparisonTolerance :
    CT18DASHIProjectionConventionResidualField

canonicalCT18DASHIProjectionConventionResidualFields :
  List CT18DASHIProjectionConventionResidualField
canonicalCT18DASHIProjectionConventionResidualFields =
  missingExternalAuthorityPayload
  ∷ missingAcceptedCT18ConventionDecision
  ∷ missingAcceptedDASHIProjectionConsumptionLaw
  ∷ missingAcceptedW4PerBinLuminosityVector
  ∷ missingAcceptedW5L43L45Luminosities
  ∷ missingAcceptedEfficiencyAcceptanceModel
  ∷ missingAcceptedSystematicBudget
  ∷ missingAcceptedNormalizationPreservationLaw
  ∷ missingAcceptedProviderToRunnerConversionLaw
  ∷ missingAcceptedComparisonTolerance
  ∷ []

data W4W5DYLuminosityAuthorityField : Set where
  acceptedPDFSetAuthority :
    W4W5DYLuminosityAuthorityField
  acceptedLHAPDFIDAuthority :
    W4W5DYLuminosityAuthorityField
  acceptedGridChecksumAuthority :
    W4W5DYLuminosityAuthorityField
  acceptedFactorizationScaleAuthority :
    W4W5DYLuminosityAuthorityField
  acceptedRapidityWindowAuthority :
    W4W5DYLuminosityAuthorityField
  acceptedMassBinIntegrationAuthority :
    W4W5DYLuminosityAuthorityField
  acceptedFlavourWeightAuthority :
    W4W5DYLuminosityAuthorityField
  acceptedLuminosityValuesAuthority :
    W4W5DYLuminosityAuthorityField
  acceptedEfficiencyAcceptanceAuthority :
    W4W5DYLuminosityAuthorityField
  acceptedSystematicBudgetAuthority :
    W4W5DYLuminosityAuthorityField
  acceptedCMSSMPPublicationPointerAuthority :
    W4W5DYLuminosityAuthorityField
  acceptedNormalizationPreservationAuthority :
    W4W5DYLuminosityAuthorityField
  acceptedConversionLawAuthority :
    W4W5DYLuminosityAuthorityField
  acceptedSourceDOIAuthority :
    W4W5DYLuminosityAuthorityField
  acceptedExternalProvenanceAuthority :
    W4W5DYLuminosityAuthorityField

record W4W5AcceptedDYLuminosityConventionDiagnostic : Set where
  field
    conventionStatus :
      W4W5DYLuminosityConventionStatus

    firstMissing :
      W4W5DYLuminosityFirstMissing

    numericStatus :
      W4W5DYLuminosityNumericStatus

    authorityReadiness :
      W4W5DYLuminosityAuthorityReadiness

    packetPath :
      String

    extractorPath :
      String

    pdfSet :
      String

    lhapdfSetID :
      String

    pdfMember :
      String

    archiveDigest :
      String

    infoDigest :
      String

    gridDigest :
      String

    sourceDOI :
      String

    conventionFormula :
      String

    binIntegration :
      String

    scaleChoice :
      String

    flavourSum :
      List String

    provenanceFields :
      List String

    requiredAuthorityFields :
      List String

    acceptedAuthorityReceiptSurface :
      List String

    missingAuthorityFields :
      List W4W5DYLuminosityAuthorityField

    ct18ProjectionBindingStatus :
      CT18DASHIProjectionConventionBindingStatus

    ct18ProjectionPacketPath :
      String

    ct18ProjectionT43ArtifactPath :
      String

    ct18ProjectionT45ArtifactPath :
      String

    ct18ProjectionBindingArtifactFields :
      List String

    ct18ProjectionResidualFields :
      List CT18DASHIProjectionConventionResidualField

    ct18ProjectionResidualFieldsAreCanonical :
      ct18ProjectionResidualFields
      ≡
      canonicalCT18DASHIProjectionConventionResidualFields

    ct18ProjectionBindingNotes :
      List String

    localCT18ProjectionPayloadPresent :
      Bool

    externalAuthorityPayloadPresent :
      Bool

    providerReadyReceiptContract :
      List String

    localProbeDisposition :
      List String

    conventionAcceptanceContract :
      List String

    firstMissingStatus :
      String

    acceptedConventionProvenance :
      String

    w5Target :
      Float

    w5TargetDecimal :
      String

    matchingTargetRatio :
      String

    matchingTargetAbsGap :
      String

    rejectedProbeRatios :
      List String

    promotesW4 :
      Bool

    promotesW5 :
      Bool

    noAcceptedConventionClaimed :
      ⊤

    noW4Promotion :
      ⊤

    noW5Promotion :
      ⊤

canonicalW4W5AcceptedDYLuminosityConventionDiagnostic :
  W4W5AcceptedDYLuminosityConventionDiagnostic
canonicalW4W5AcceptedDYLuminosityConventionDiagnostic =
  record
    { conventionStatus =
        candidateLocalCT18NLOConventionNotAccepted
    ; firstMissing =
        missingAcceptedDYLuminosityConventionAuthority
    ; numericStatus =
        localCandidateDoesNotMatchW5Target
    ; authorityReadiness =
        acceptedAuthorityReceiptMissing
    ; packetPath =
        "scripts/data/pdf/ct18_dashi_pdf_packet.json"
    ; extractorPath =
        "scripts/extract_ct18_pdf_packet.py"
    ; pdfSet =
        "CT18NLO SetIndex 14400"
    ; lhapdfSetID =
        "LHAPDF set id 14400 / CT18NLO"
    ; pdfMember =
        "member 0 central value; CT18NLO has 59 members and hessian 90 percent error sets"
    ; archiveDigest =
        "c9127231e77e97cbec79cb5839203ab00f8db77237a061b61f9420f2b7b9c213"
    ; infoDigest =
        "be60232d8e6c49982c82f5fa990fd5b0fd1050719944f31602bf27cdb16548b0"
    ; gridDigest =
        "375db856d2f8c7087a626c92ebf228d3f080e5de83175519778ffaf6e72e5410"
    ; sourceDOI =
        "missing accepted source DOI receipt; CT18NLO info currently records arXiv:1908.11394 only"
    ; conventionFormula =
        "integral dlog(x1) sum_q e_q^2 [q(x1,Q) qbar(tau/x1,Q) + qbar(x1,Q) q(tau/x1,Q)] with tau = M^2/s"
    ; binIntegration =
        "trapezoid in log(x1) with n_x = 200, then trapezoid in mass with n_m = 80 over each CMS-SMP-20-003 mass window"
    ; scaleChoice =
        "Q = dilepton mass for each center/window integration point; sqrt_s = 13000 GeV; eta_cut = 2.4"
    ; flavourSum =
        "u with charge weight 4/9"
        ∷ "d with charge weight 1/9"
        ∷ "s with charge weight 1/9"
        ∷ "q qbar plus qbar q symmetrisation"
        ∷ "LHAPDF lhagrid1 x*f(x,Q) divided by x before luminosity formation"
        ∷ []
    ; provenanceFields =
        "CT18NLO info Reference: arXiv:1908.11394 (temporary)"
        ∷ "CT18NLO Authors: T.-J. Hou, K. Xie, J. Gao, S. Dulat, M. Guzzi, T. J. Hobbs, J. Huston, P. Nadolsky, J. Pumplin, C. Schmidt, I. Sitiwaldi, D. Stump, C.-P. Yuan"
        ∷ "Format lhagrid1; OrderQCD 1; AlphaS_MZ 0.118000; AlphaS_OrderQCD 1"
        ∷ "archive, info, and central grid SHA-256 digests are recorded in the packet"
        ∷ []
    ; requiredAuthorityFields =
        "PDF set authority: CT18NLO or accepted alternative family/version"
        ∷ "LHAPDF id authority: set id 14400 or accepted replacement id"
        ∷ "grid checksum authority: accepted .info/.dat or provider-table SHA-256 receipt"
        ∷ "factorization scale convention authority: Q = M or accepted Q2 alternative"
        ∷ "rapidity-window authority: eta/y acceptance and lepton/boson convention"
        ∷ "mass-bin integration prescription for CMS-SMP-20-003 phi-star windows"
        ∷ "flavour-weight rule authority including charge weights and heavy-flavour treatment"
        ∷ "luminosity values authority for W5 L43/L45 and the W4 per-bin ell_i vector, or an accepted reproducible provider route for those values"
        ∷ "efficiency/acceptance model authority tying the luminosity convention to CMS-SMP fiducial bins and detector corrections"
        ∷ "systematic budget authority for PDF, scale, alphaS, EW/QED/FSR, acceptance, efficiency, and numerical integration uncertainties"
        ∷ "CMS-SMP publication pointer authority naming analysis id, DOI/arXiv/public page, table/bin mapping, and revision"
        ∷ "normalization-preservation law authority showing that provider-to-runner conversion preserves the accepted normalization"
        ∷ "conversion law authority mapping provider fields to W4 ell_i and W5 L45/L43 runner inputs"
        ∷ "source DOI authority for the PDF/convention source"
        ∷ "external authority/provenance receipt naming provider, command/API, inputs, checksums, and timestamp"
        ∷ []
    ; acceptedAuthorityReceiptSurface =
        "missingAcceptedDYLuminosityConventionAuthority requires accepted PDF set"
        ∷ "missingAcceptedDYLuminosityConventionAuthority requires accepted LHAPDF id"
        ∷ "missingAcceptedDYLuminosityConventionAuthority requires accepted grid checksum"
        ∷ "missingAcceptedDYLuminosityConventionAuthority requires accepted factorization scale convention"
        ∷ "missingAcceptedDYLuminosityConventionAuthority requires accepted rapidity window"
        ∷ "missingAcceptedDYLuminosityConventionAuthority requires accepted mass-bin integration rule"
        ∷ "missingAcceptedDYLuminosityConventionAuthority requires accepted flavour-weight rule"
        ∷ "missingAcceptedDYLuminosityConventionAuthority requires accepted luminosity values or an accepted provider computation route"
        ∷ "missingAcceptedDYLuminosityConventionAuthority requires accepted efficiency/acceptance model"
        ∷ "missingAcceptedDYLuminosityConventionAuthority requires accepted systematic budget"
        ∷ "missingAcceptedDYLuminosityConventionAuthority requires accepted CMS-SMP publication pointer and bin mapping"
        ∷ "missingAcceptedDYLuminosityConventionAuthority requires accepted normalization-preservation law"
        ∷ "missingAcceptedDYLuminosityConventionAuthority requires accepted conversion law for W4/W5 runners"
        ∷ "missingAcceptedDYLuminosityConventionAuthority requires accepted source DOI"
        ∷ "missingAcceptedDYLuminosityConventionAuthority requires accepted external authority/provenance"
        ∷ []
    ; missingAuthorityFields =
        acceptedPDFSetAuthority
        ∷ acceptedLHAPDFIDAuthority
        ∷ acceptedGridChecksumAuthority
        ∷ acceptedFactorizationScaleAuthority
        ∷ acceptedRapidityWindowAuthority
        ∷ acceptedMassBinIntegrationAuthority
        ∷ acceptedFlavourWeightAuthority
        ∷ acceptedLuminosityValuesAuthority
        ∷ acceptedEfficiencyAcceptanceAuthority
        ∷ acceptedSystematicBudgetAuthority
        ∷ acceptedCMSSMPPublicationPointerAuthority
        ∷ acceptedNormalizationPreservationAuthority
        ∷ acceptedConversionLawAuthority
        ∷ acceptedSourceDOIAuthority
        ∷ acceptedExternalProvenanceAuthority
        ∷ []
    ; ct18ProjectionBindingStatus =
        localCT18GridConventionBoundToProjectionArtifactsCandidateOnly
    ; ct18ProjectionPacketPath =
        "scripts/data/pdf/ct18_dashi_pdf_packet.json"
    ; ct18ProjectionT43ArtifactPath =
        "scripts/data/outputs/t43_projection_v4.json"
    ; ct18ProjectionT45ArtifactPath =
        "scripts/data/outputs/t45_projection_v4.json"
    ; ct18ProjectionBindingArtifactFields =
        "ct18 packet: accepted_dy_luminosity_convention_status = candidate_local_ct18nlo_convention_not_accepted"
        ∷ "ct18 packet: W4W5_luminosity_convention formula, mass windows, scale choice, eta_cut, flavour weights, n_x, and n_m are locally recorded"
        ∷ "ct18 packet: W4_luminosity_shape contains local candidate per-bin luminosity proxies, not accepted ell_i values"
        ∷ "ct18 packet: W5 luminosity ratios are recorded for fixed-x, t45/z_peak, and t45/t43 negative probes"
        ∷ "t43 projection artifact: dashi-hepdata-t43-projection-v1 JSON with R_dashi, R_data, residuals, and bin bindings"
        ∷ "t45 projection artifact: dashi-hepdata-t43-projection-v1 JSON with R_dashi, R_data, residuals, and bin bindings for the above-Z surface"
        ∷ []
    ; ct18ProjectionResidualFields =
        canonicalCT18DASHIProjectionConventionResidualFields
    ; ct18ProjectionResidualFieldsAreCanonical =
        refl
    ; ct18ProjectionBindingNotes =
        "The local CT18 grid convention is now bound to the DASHI projection artifact paths as candidate provenance"
        ∷ "This binding is not an external PDF authority claim and does not accept the CT18 luminosity convention"
        ∷ "The W4 per-bin values in the packet are local luminosity proxies; they are not accepted provider ell_i inputs"
        ∷ "The W5 L43/L45 values are local diagnostics; no provider has accepted them as runner inputs"
        ∷ "DASHI projection consumption still needs an accepted normalization-preservation and provider-to-runner conversion law"
        ∷ []
    ; localCT18ProjectionPayloadPresent =
        true
    ; externalAuthorityPayloadPresent =
        false
    ; providerReadyReceiptContract =
        "provider receipt must explicitly say whether this candidate formula is accepted, replaced, or rejected"
        ∷ "provider receipt must bind each accepted field to a source path, DOI, checksum, command/API, and timestamp"
        ∷ "provider receipt must expose the exact W4/W5 runner packet fields: luminosities, efficiency/acceptance, systematic budget, CMS-SMP pointer, normalization preservation, and conversion law"
        ∷ "provider receipt must distinguish convention authority from numeric agreement; numeric ratios alone cannot inhabit the authority"
        ∷ "provider receipt must preserve the rejected local CT18 probes as diagnostics unless an authority supersedes them"
        ∷ "provider receipt must leave promotesW4 = false and promotesW5 = false until downstream W4/W5 checks are separately proved"
        ∷ []
    ; localProbeDisposition =
        "local fixed-x CT18NLO probe is falsified against the W5 target, not an accepted convention"
        ∷ "local rapidity-window t45/z_peak CT18NLO probe is falsified against the W5 target, not an accepted convention"
        ∷ "local rapidity-window t45/t43 CT18NLO denominator hypothesis is falsified against the W5 target"
        ∷ "local CT18NLO digests, formula, and integration settings are candidate provenance only"
        ∷ []
    ; conventionAcceptanceContract =
        "accepted convention must name the provider or repo authority that accepts this exact DY luminosity definition"
        ∷ "accepted convention must bind the 50-76, 76-106, and 106-170 GeV CMS-SMP-20-003 windows to an integration rule rather than a center-only proxy"
        ∷ "accepted convention must decide Q versus Q2 notation and whether Q = M is admissible for every mass integration point"
        ∷ "accepted convention must state whether c/b channels are excluded, included, or assigned a separate heavy-flavour systematic"
        ∷ "accepted convention must specify CT18NLO member/error-set handling before any W4/W5 tolerance can be evaluated"
        ∷ "accepted convention must bind luminosity, efficiency/acceptance, systematic budget, CMS-SMP publication pointer, normalization preservation, and conversion law before runner ingestion"
        ∷ "accepted convention must provide a provenance receipt before W4 shape adequacy or W5 t45 promotion can be claimed"
        ∷ []
    ; firstMissingStatus =
        "first missing: accepted Drell-Yan luminosity convention authority/provenance for W4/W5, including luminosity values, efficiency/acceptance model, systematic budget, CMS-SMP pointer, normalization preservation, and conversion law; local CT18NLO candidate is recorded but not accepted"
    ; acceptedConventionProvenance =
        "none present in repo-local packet; only candidate formula, digests, and rejected numeric probes are recorded"
    ; w5Target =
        0.8804486068
    ; w5TargetDecimal =
        "0.8804486068"
    ; matchingTargetRatio =
        "0.7514043986785174"
    ; matchingTargetAbsGap =
        "0.12904420812148265"
    ; rejectedProbeRatios =
        "fixed-x u-quark xfxQ ratio = 1.0506681065158017; abs gap = 0.17021949971580164"
        ∷ "rapidity-window t45/z_peak ratio = 0.7514043986785174; abs gap = 0.12904420812148265"
        ∷ "rapidity-window t45/t43 ratio = 0.3348750784006896; abs gap = 0.5455735283993104"
        ∷ []
    ; promotesW4 =
        false
    ; promotesW5 =
        false
    ; noAcceptedConventionClaimed =
        tt
    ; noW4Promotion =
        tt
    ; noW5Promotion =
        tt
    }

canonicalW4W5DYLuminosityFirstMissing :
  W4W5AcceptedDYLuminosityConventionDiagnostic.firstMissing
    canonicalW4W5AcceptedDYLuminosityConventionDiagnostic
    ≡
  missingAcceptedDYLuminosityConventionAuthority
canonicalW4W5DYLuminosityFirstMissing =
  refl

canonicalW4W5DYLuminosityDoesNotPromoteW4 :
  W4W5AcceptedDYLuminosityConventionDiagnostic.promotesW4
    canonicalW4W5AcceptedDYLuminosityConventionDiagnostic
    ≡
  false
canonicalW4W5DYLuminosityDoesNotPromoteW4 =
  refl

canonicalW4W5DYLuminosityDoesNotPromoteW5 :
  W4W5AcceptedDYLuminosityConventionDiagnostic.promotesW5
    canonicalW4W5AcceptedDYLuminosityConventionDiagnostic
    ≡
  false
canonicalW4W5DYLuminosityDoesNotPromoteW5 =
  refl
