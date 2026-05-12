module DASHI.Physics.Closure.AcceptedDYLuminosityConventionAuthorityReceipt where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Unit using (⊤; tt)
open import Agda.Primitive using (Setω)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.W4W5AcceptedDYLuminosityConventionDiagnostic as DY

------------------------------------------------------------------------
-- Accepted DY luminosity convention authority response intake.
--
-- This module is a non-promoting receipt skeleton.  It records the exact
-- provider-response payload required to turn an external answer into a later
-- accepted-convention path, but the canonical local value below remains
-- insufficient because no external provider answer has been supplied.

data AcceptedDYLuminosityConventionAuthority : Set where

acceptedDYLuminosityConventionAuthorityImpossibleHere :
  AcceptedDYLuminosityConventionAuthority →
  ⊥
acceptedDYLuminosityConventionAuthorityImpossibleHere ()

data DYLuminosityAuthorityResponseIntakeStatus : Set where
  awaitingProviderResponse :
    DYLuminosityAuthorityResponseIntakeStatus
  providerResponseRecordedNonPromoting :
    DYLuminosityAuthorityResponseIntakeStatus

data DYLuminosityAuthorityResponseStatus : Set where
  accepted :
    DYLuminosityAuthorityResponseStatus
  rejected :
    DYLuminosityAuthorityResponseStatus
  insufficient :
    DYLuminosityAuthorityResponseStatus

data DYLuminosityAuthorityResponseClass : Set where
  acceptedLocalCandidateConvention :
    DYLuminosityAuthorityResponseClass
  replacementConvention :
    DYLuminosityAuthorityResponseClass
  rejectedConventionRequest :
    DYLuminosityAuthorityResponseClass
  insufficientConventionResponse :
    DYLuminosityAuthorityResponseClass

data DYLuminosityAuthorityPayloadField : Set where
  provider_name :
    DYLuminosityAuthorityPayloadField
  provider_role :
    DYLuminosityAuthorityPayloadField
  pdf_set_version :
    DYLuminosityAuthorityPayloadField
  lhapdf_id :
    DYLuminosityAuthorityPayloadField
  member_id :
    DYLuminosityAuthorityPayloadField
  grid_checksum :
    DYLuminosityAuthorityPayloadField
  scale_convention :
    DYLuminosityAuthorityPayloadField
  rapidity_window :
    DYLuminosityAuthorityPayloadField
  mass_bin_rule :
    DYLuminosityAuthorityPayloadField
  flavour_weight_rule :
    DYLuminosityAuthorityPayloadField
  integration_method :
    DYLuminosityAuthorityPayloadField
  luminosity_values :
    DYLuminosityAuthorityPayloadField
  efficiency_acceptance_model :
    DYLuminosityAuthorityPayloadField
  systematic_budget :
    DYLuminosityAuthorityPayloadField
  cms_smp_publication_pointer :
    DYLuminosityAuthorityPayloadField
  normalization_preservation_law :
    DYLuminosityAuthorityPayloadField
  conversion_law :
    DYLuminosityAuthorityPayloadField
  source_citation :
    DYLuminosityAuthorityPayloadField
  attestation_no_manual_overfit :
    DYLuminosityAuthorityPayloadField
  status :
    DYLuminosityAuthorityPayloadField

canonicalDYLuminosityAuthorityPayloadFields :
  List DYLuminosityAuthorityPayloadField
canonicalDYLuminosityAuthorityPayloadFields =
  provider_name
  ∷ provider_role
  ∷ pdf_set_version
  ∷ lhapdf_id
  ∷ member_id
  ∷ grid_checksum
  ∷ scale_convention
  ∷ rapidity_window
  ∷ mass_bin_rule
  ∷ flavour_weight_rule
  ∷ integration_method
  ∷ luminosity_values
  ∷ efficiency_acceptance_model
  ∷ systematic_budget
  ∷ cms_smp_publication_pointer
  ∷ normalization_preservation_law
  ∷ conversion_law
  ∷ source_citation
  ∷ attestation_no_manual_overfit
  ∷ status
  ∷ []

record DYLuminosityAuthorityProviderResponsePayload : Set where
  field
    providerName :
      String

    providerRole :
      String

    pdfSetVersion :
      String

    lhapdfID :
      String

    memberID :
      String

    gridChecksum :
      String

    scaleConvention :
      String

    rapidityWindow :
      String

    massBinRule :
      String

    flavourWeightRule :
      String

    integrationMethod :
      String

    luminosityValues :
      String

    efficiencyAcceptanceModel :
      String

    systematicBudget :
      String

    cmsSMPPublicationPointer :
      String

    normalizationPreservationLaw :
      String

    conversionLaw :
      String

    sourceCitation :
      String

    attestationNoManualOverfit :
      String

    responseStatus :
      DYLuminosityAuthorityResponseStatus

record AcceptedDYLuminosityConventionAuthorityReceipt : Setω where
  field
    intakeStatus :
      DYLuminosityAuthorityResponseIntakeStatus

    responseStatus :
      DYLuminosityAuthorityResponseStatus

    responseClass :
      DYLuminosityAuthorityResponseClass

    requestPacketPath :
      String

    responseTemplatePath :
      String

    diagnostic :
      DY.W4W5AcceptedDYLuminosityConventionDiagnostic

    authorityFirstMissing :
      DY.W4W5DYLuminosityFirstMissing

    requiredPayloadFields :
      List DYLuminosityAuthorityPayloadField

    requiredPayloadFieldsAreCanonical :
      requiredPayloadFields
      ≡
      canonicalDYLuminosityAuthorityPayloadFields

    requiredPayloadFieldLabels :
      List String

    ct18ProjectionBindingStatus :
      DY.CT18DASHIProjectionConventionBindingStatus

    ct18ProjectionPacketPath :
      String

    ct18ProjectionT43ArtifactPath :
      String

    ct18ProjectionT45ArtifactPath :
      String

    ct18ProjectionResidualFields :
      List DY.CT18DASHIProjectionConventionResidualField

    ct18ProjectionResidualFieldsAreCanonical :
      ct18ProjectionResidualFields
      ≡
      DY.canonicalCT18DASHIProjectionConventionResidualFields

    ct18ProjectionBindingNotes :
      List String

    acceptedOrReplacementPayloadContract :
      List String

    rejectionOrInsufficientPayloadContract :
      List String

    providerName :
      String

    providerRole :
      String

    pdfSetVersion :
      String

    lhapdfID :
      String

    memberID :
      String

    gridChecksum :
      String

    scaleConvention :
      String

    rapidityWindow :
      String

    massBinRule :
      String

    flavourWeightRule :
      String

    integrationMethod :
      String

    luminosityValues :
      String

    efficiencyAcceptanceModel :
      String

    systematicBudget :
      String

    cmsSMPPublicationPointer :
      String

    normalizationPreservationLaw :
      String

    conversionLaw :
      String

    sourceCitation :
      String

    attestationNoManualOverfit :
      String

    firstMissingStatus :
      String

    externalProviderAnswerPresent :
      Bool

    acceptedAuthorityConstructed :
      Bool

    promotesW4 :
      Bool

    promotesW5 :
      Bool

    noSyntheticAuthority :
      ⊤

    noAcceptedConventionClaimed :
      ⊤

    noW4Promotion :
      ⊤

    noW5Promotion :
      ⊤

    acceptedAuthorityImpossibleHere :
      AcceptedDYLuminosityConventionAuthority →
      ⊥

canonicalAcceptedDYLuminosityConventionAuthorityReceipt :
  AcceptedDYLuminosityConventionAuthorityReceipt
canonicalAcceptedDYLuminosityConventionAuthorityReceipt =
  record
    { intakeStatus =
        awaitingProviderResponse
    ; responseStatus =
        insufficient
    ; responseClass =
        insufficientConventionResponse
    ; requestPacketPath =
        "Docs/AcceptedDYLuminosityConventionAuthorityProviderPacket.md"
    ; responseTemplatePath =
        "Docs/AcceptedDYLuminosityConventionAuthorityResponse.md"
    ; diagnostic =
        DY.canonicalW4W5AcceptedDYLuminosityConventionDiagnostic
    ; authorityFirstMissing =
        DY.missingAcceptedDYLuminosityConventionAuthority
    ; requiredPayloadFields =
        canonicalDYLuminosityAuthorityPayloadFields
    ; requiredPayloadFieldsAreCanonical =
        refl
    ; requiredPayloadFieldLabels =
        "provider_name"
        ∷ "provider_role"
        ∷ "pdf_set_version"
        ∷ "lhapdf_id"
        ∷ "member_id"
        ∷ "grid_checksum"
        ∷ "scale_convention"
        ∷ "rapidity_window"
        ∷ "mass_bin_rule"
        ∷ "flavour_weight_rule"
        ∷ "integration_method"
        ∷ "luminosity_values"
        ∷ "efficiency_acceptance_model"
        ∷ "systematic_budget"
        ∷ "cms_smp_publication_pointer"
        ∷ "normalization_preservation_law"
        ∷ "conversion_law"
        ∷ "source_citation"
        ∷ "attestation_no_manual_overfit"
        ∷ "status accepted/rejected/insufficient"
        ∷ []
    ; ct18ProjectionBindingStatus =
        DY.localCT18GridConventionBoundToProjectionArtifactsCandidateOnly
    ; ct18ProjectionPacketPath =
        DY.W4W5AcceptedDYLuminosityConventionDiagnostic.ct18ProjectionPacketPath
          DY.canonicalW4W5AcceptedDYLuminosityConventionDiagnostic
    ; ct18ProjectionT43ArtifactPath =
        DY.W4W5AcceptedDYLuminosityConventionDiagnostic.ct18ProjectionT43ArtifactPath
          DY.canonicalW4W5AcceptedDYLuminosityConventionDiagnostic
    ; ct18ProjectionT45ArtifactPath =
        DY.W4W5AcceptedDYLuminosityConventionDiagnostic.ct18ProjectionT45ArtifactPath
          DY.canonicalW4W5AcceptedDYLuminosityConventionDiagnostic
    ; ct18ProjectionResidualFields =
        DY.canonicalCT18DASHIProjectionConventionResidualFields
    ; ct18ProjectionResidualFieldsAreCanonical =
        refl
    ; ct18ProjectionBindingNotes =
        DY.W4W5AcceptedDYLuminosityConventionDiagnostic.ct18ProjectionBindingNotes
          DY.canonicalW4W5AcceptedDYLuminosityConventionDiagnostic
    ; acceptedOrReplacementPayloadContract =
        "accepted response: provider accepts the convention and supplies all required fields with provenance"
        ∷ "replacement response: provider rejects the local candidate and supplies a complete replacement convention with the same required fields"
        ∷ "accepted or replacement payloads must supply luminosity values for W5 L43/L45 and the W4 per-bin luminosity vector, or name an accepted provider route that computes them without local tuning"
        ∷ "accepted or replacement payloads must bind efficiency/acceptance, systematic budget, CMS-SMP publication pointer, normalization preservation, and conversion law before W4/W5 runners consume the packet"
        ∷ "accepted or replacement payloads are external inputs only; this canonical receipt does not manufacture them"
        ∷ "downstream W4/W5 receipts may consume an accepted external payload only after separate validation of provenance, checksums, convention fields, and no-manual-overfit attestation"
        ∷ []
    ; rejectionOrInsufficientPayloadContract =
        "rejected response: provider rejects the request and names exact invalid or missing fields"
        ∷ "insufficient response: one or more provider identity, role, PDF, checksum, convention, luminosity, efficiency/acceptance, systematic, CMS-SMP pointer, normalization, conversion, citation, attestation, or status fields are missing"
        ∷ "the current canonical local response is insufficient because the external provider answer is missing"
        ∷ []
    ; providerName =
        "missing external provider answer"
    ; providerRole =
        "missing"
    ; pdfSetVersion =
        "missing"
    ; lhapdfID =
        "missing"
    ; memberID =
        "missing"
    ; gridChecksum =
        "missing"
    ; scaleConvention =
        "missing"
    ; rapidityWindow =
        "missing"
    ; massBinRule =
        "missing"
    ; flavourWeightRule =
        "missing"
    ; integrationMethod =
        "missing"
    ; luminosityValues =
        "missing accepted W5 L43/L45 luminosities and W4 per-bin luminosity vector"
    ; efficiencyAcceptanceModel =
        "missing accepted efficiency/acceptance model tying provider luminosities to CMS-SMP bins"
    ; systematicBudget =
        "missing accepted systematic budget for PDF, scale, alphaS, EW/QED/FSR, acceptance, efficiency, and numerical integration uncertainties"
    ; cmsSMPPublicationPointer =
        "missing accepted CMS-SMP publication pointer, analysis id, DOI/arXiv/public page, table/bin mapping, and revision"
    ; normalizationPreservationLaw =
        "missing law proving or attesting that conversion preserves the provider normalization used by W4/W5"
    ; conversionLaw =
        "missing law from provider convention fields to the W4 ell_i vector and W5 L45/L43 ratio inputs"
    ; sourceCitation =
        "missing"
    ; attestationNoManualOverfit =
        "missing"
    ; firstMissingStatus =
        "first missing remains missingAcceptedDYLuminosityConventionAuthority; no external provider answer has supplied luminosity values, efficiency/acceptance model, systematic budget, CMS-SMP publication pointer, normalization preservation law, conversion law, and provenance"
    ; externalProviderAnswerPresent =
        false
    ; acceptedAuthorityConstructed =
        false
    ; promotesW4 =
        false
    ; promotesW5 =
        false
    ; noSyntheticAuthority =
        tt
    ; noAcceptedConventionClaimed =
        tt
    ; noW4Promotion =
        tt
    ; noW5Promotion =
        tt
    ; acceptedAuthorityImpossibleHere =
        acceptedDYLuminosityConventionAuthorityImpossibleHere
    }

canonicalAcceptedDYLuminosityConventionAuthorityReceiptStillAwaiting :
  AcceptedDYLuminosityConventionAuthorityReceipt.intakeStatus
    canonicalAcceptedDYLuminosityConventionAuthorityReceipt
    ≡
  awaitingProviderResponse
canonicalAcceptedDYLuminosityConventionAuthorityReceiptStillAwaiting =
  refl

canonicalAcceptedDYLuminosityConventionAuthorityReceiptInsufficient :
  AcceptedDYLuminosityConventionAuthorityReceipt.responseStatus
    canonicalAcceptedDYLuminosityConventionAuthorityReceipt
    ≡
  insufficient
canonicalAcceptedDYLuminosityConventionAuthorityReceiptInsufficient =
  refl

canonicalAcceptedDYLuminosityConventionAuthorityFirstMissing :
  AcceptedDYLuminosityConventionAuthorityReceipt.authorityFirstMissing
    canonicalAcceptedDYLuminosityConventionAuthorityReceipt
    ≡
  DY.missingAcceptedDYLuminosityConventionAuthority
canonicalAcceptedDYLuminosityConventionAuthorityFirstMissing =
  refl
