module DASHI.Biology.TraumaClinicalGovernanceBoundary where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Setω)

import DASHI.Biology.BioactiveAuthorityBoundaryCore as Bioactive
import DASHI.Promotion.AuthorityBoundaryCore as AuthorityBoundary
import Ontology.ClinicalDiagnostics.ClinicalDiagnosticsCore as Clinical

------------------------------------------------------------------------
-- Trauma/body-memory clinical governance boundary.
--
-- This module is intentionally candidate-only.  It names a clinically
-- conservative boundary for trauma/body-memory adjacent modules and keeps
-- the local surface fail-closed:
--
--   - no diagnosis authority,
--   - no treatment prescription authority,
--   - no exposure-forcing authority,
--   - no vulnerable-user authority,
--   - explicit consent, pacing, and review gates.
--
-- The record reuses canonical receipts from the repository's clinical
-- diagnostics and bioactive boundary cores so downstream consumers can
-- thread the boundary surface without bypassing those authorities.

data TraumaClinicalGovernanceAxis : Set where
  traumaCandidateAxis :
    TraumaClinicalGovernanceAxis

  bodyMemoryCandidateAxis :
    TraumaClinicalGovernanceAxis

  consentGateAxis :
    TraumaClinicalGovernanceAxis

  pacingGateAxis :
    TraumaClinicalGovernanceAxis

  reviewGateAxis :
    TraumaClinicalGovernanceAxis

  diagnosisBlockedAxis :
    TraumaClinicalGovernanceAxis

  treatmentPrescriptionBlockedAxis :
    TraumaClinicalGovernanceAxis

  exposureForcingBlockedAxis :
    TraumaClinicalGovernanceAxis

  vulnerableUserAuthorityBlockedAxis :
    TraumaClinicalGovernanceAxis

canonicalTraumaClinicalGovernanceAxes :
  List TraumaClinicalGovernanceAxis
canonicalTraumaClinicalGovernanceAxes =
  traumaCandidateAxis
  ∷ bodyMemoryCandidateAxis
  ∷ consentGateAxis
  ∷ pacingGateAxis
  ∷ reviewGateAxis
  ∷ diagnosisBlockedAxis
  ∷ treatmentPrescriptionBlockedAxis
  ∷ exposureForcingBlockedAxis
  ∷ vulnerableUserAuthorityBlockedAxis
  ∷ []

canonicalTraumaClinicalGovernanceNotes :
  List String
canonicalTraumaClinicalGovernanceNotes =
  "Trauma/body-memory modules remain candidate-only and do not assert diagnosis authority"
  ∷ "Treatment prescription authority is absent and must not be inferred from the boundary surface"
  ∷ "Exposure forcing authority is absent and any exposure work requires separate consented review"
  ∷ "Vulnerable-user authority is absent; the surface does not authorise coercive or paternalistic control"
  ∷ "Consent, pacing, and review are explicit gates rather than ambient assumptions"
  ∷ "Clinical diagnostics and bioactive authority are reused only as canonical receipts"
  ∷ "The boundary remains fail-closed for promotion, prescription, and coercion"
  ∷ []

record TraumaClinicalGovernanceBoundary : Setω where
  field
    clinicalDiagnosticsCoreReceipt :
      Clinical.ClinicalDiagnosticsCore

    clinicalDiagnosticsCoreBoundaryOnlyIsFalse :
      Clinical.boundaryOnly clinicalDiagnosticsCoreReceipt ≡ false

    bioactiveAuthorityBoundaryCoreReceipt :
      Bioactive.BioactiveAuthorityBoundaryCore

    bioactiveAuthorityBoundaryCorePromotedIsFalse :
      AuthorityBoundary.receiptBoundaryPromoted
        (Bioactive.genericAuthorityBoundaryReceipt
          bioactiveAuthorityBoundaryCoreReceipt)
      ≡
      false

    traumaCandidateOnly :
      Bool

    traumaCandidateOnlyIsTrue :
      traumaCandidateOnly ≡ true

    bodyMemoryCandidateOnly :
      Bool

    bodyMemoryCandidateOnlyIsTrue :
      bodyMemoryCandidateOnly ≡ true

    diagnosisAuthority :
      Bool

    diagnosisAuthorityIsFalse :
      diagnosisAuthority ≡ false

    treatmentPrescriptionAuthority :
      Bool

    treatmentPrescriptionAuthorityIsFalse :
      treatmentPrescriptionAuthority ≡ false

    exposureForcingAuthority :
      Bool

    exposureForcingAuthorityIsFalse :
      exposureForcingAuthority ≡ false

    vulnerableUserAuthority :
      Bool

    vulnerableUserAuthorityIsFalse :
      vulnerableUserAuthority ≡ false

    consentGateRequired :
      Bool

    consentGateRequiredIsTrue :
      consentGateRequired ≡ true

    pacingGateRequired :
      Bool

    pacingGateRequiredIsTrue :
      pacingGateRequired ≡ true

    reviewGateRequired :
      Bool

    reviewGateRequiredIsTrue :
      reviewGateRequired ≡ true

    traumaClaimReceipt :
      String

    bodyMemoryClaimReceipt :
      String

    diagnosisBlockedReceipt :
      String

    treatmentBlockedReceipt :
      String

    exposureBlockedReceipt :
      String

    vulnerableAuthorityBlockedReceipt :
      String

    consentGateReceipt :
      String

    pacingGateReceipt :
      String

    reviewGateReceipt :
      String

    governanceAxes :
      List TraumaClinicalGovernanceAxis

    governanceAxesAreCanonical :
      governanceAxes ≡ canonicalTraumaClinicalGovernanceAxes

    governingNotes :
      List String

    governingNotesAreCanonical :
      governingNotes ≡ canonicalTraumaClinicalGovernanceNotes

open TraumaClinicalGovernanceBoundary public

canonicalTraumaClinicalGovernanceBoundary :
  TraumaClinicalGovernanceBoundary
canonicalTraumaClinicalGovernanceBoundary =
  record
    { clinicalDiagnosticsCoreReceipt =
        Clinical.canonicalClinicalDiagnosticsCore
    ; clinicalDiagnosticsCoreBoundaryOnlyIsFalse =
        Clinical.canonicalClinicalDiagnosticsCoreIsBoundaryOnly
    ; bioactiveAuthorityBoundaryCoreReceipt =
        Bioactive.canonicalBioactiveAuthorityBoundaryCore
    ; bioactiveAuthorityBoundaryCorePromotedIsFalse =
        refl
    ; traumaCandidateOnly =
        true
    ; traumaCandidateOnlyIsTrue =
        refl
    ; bodyMemoryCandidateOnly =
        true
    ; bodyMemoryCandidateOnlyIsTrue =
        refl
    ; diagnosisAuthority =
        false
    ; diagnosisAuthorityIsFalse =
        refl
    ; treatmentPrescriptionAuthority =
        false
    ; treatmentPrescriptionAuthorityIsFalse =
        refl
    ; exposureForcingAuthority =
        false
    ; exposureForcingAuthorityIsFalse =
        refl
    ; vulnerableUserAuthority =
        false
    ; vulnerableUserAuthorityIsFalse =
        refl
    ; consentGateRequired =
        true
    ; consentGateRequiredIsTrue =
        refl
    ; pacingGateRequired =
        true
    ; pacingGateRequiredIsTrue =
        refl
    ; reviewGateRequired =
        true
    ; reviewGateRequiredIsTrue =
        refl
    ; traumaClaimReceipt =
        "trauma candidate-only clinical governance boundary"
    ; bodyMemoryClaimReceipt =
        "body-memory candidate-only clinical governance boundary"
    ; diagnosisBlockedReceipt =
        "diagnosis authority is blocked at the boundary"
    ; treatmentBlockedReceipt =
        "treatment prescription authority is blocked at the boundary"
    ; exposureBlockedReceipt =
        "exposure forcing authority is blocked at the boundary"
    ; vulnerableAuthorityBlockedReceipt =
        "vulnerable-user authority is blocked at the boundary"
    ; consentGateReceipt =
        "consent gate required before any trauma-adjacent review"
    ; pacingGateReceipt =
        "pacing gate required before any trauma-adjacent review"
    ; reviewGateReceipt =
        "review gate required before any trauma-adjacent review"
    ; governanceAxes =
        canonicalTraumaClinicalGovernanceAxes
    ; governanceAxesAreCanonical =
        refl
    ; governingNotes =
        canonicalTraumaClinicalGovernanceNotes
    ; governingNotesAreCanonical =
        refl
    }

canonicalTraumaClinicalGovernanceBoundaryClinicalDiagnosticsBoundaryOnlyIsFalse :
  Clinical.boundaryOnly
    (clinicalDiagnosticsCoreReceipt canonicalTraumaClinicalGovernanceBoundary)
  ≡
  false
canonicalTraumaClinicalGovernanceBoundaryClinicalDiagnosticsBoundaryOnlyIsFalse =
  clinicalDiagnosticsCoreBoundaryOnlyIsFalse canonicalTraumaClinicalGovernanceBoundary

canonicalTraumaClinicalGovernanceBoundaryBioactiveBoundaryPromotedIsFalse :
  AuthorityBoundary.receiptBoundaryPromoted
    (Bioactive.genericAuthorityBoundaryReceipt
      (bioactiveAuthorityBoundaryCoreReceipt
        canonicalTraumaClinicalGovernanceBoundary))
  ≡
  false
canonicalTraumaClinicalGovernanceBoundaryBioactiveBoundaryPromotedIsFalse =
  bioactiveAuthorityBoundaryCorePromotedIsFalse canonicalTraumaClinicalGovernanceBoundary

canonicalTraumaCandidateOnlyIsTrue :
  traumaCandidateOnly canonicalTraumaClinicalGovernanceBoundary ≡ true
canonicalTraumaCandidateOnlyIsTrue =
  traumaCandidateOnlyIsTrue canonicalTraumaClinicalGovernanceBoundary

canonicalBodyMemoryCandidateOnlyIsTrue :
  bodyMemoryCandidateOnly canonicalTraumaClinicalGovernanceBoundary ≡ true
canonicalBodyMemoryCandidateOnlyIsTrue =
  bodyMemoryCandidateOnlyIsTrue canonicalTraumaClinicalGovernanceBoundary

canonicalDiagnosisAuthorityIsFalse :
  diagnosisAuthority canonicalTraumaClinicalGovernanceBoundary ≡ false
canonicalDiagnosisAuthorityIsFalse =
  diagnosisAuthorityIsFalse canonicalTraumaClinicalGovernanceBoundary

canonicalTreatmentPrescriptionAuthorityIsFalse :
  treatmentPrescriptionAuthority canonicalTraumaClinicalGovernanceBoundary ≡ false
canonicalTreatmentPrescriptionAuthorityIsFalse =
  treatmentPrescriptionAuthorityIsFalse canonicalTraumaClinicalGovernanceBoundary

canonicalExposureForcingAuthorityIsFalse :
  exposureForcingAuthority canonicalTraumaClinicalGovernanceBoundary ≡ false
canonicalExposureForcingAuthorityIsFalse =
  exposureForcingAuthorityIsFalse canonicalTraumaClinicalGovernanceBoundary

canonicalVulnerableUserAuthorityIsFalse :
  vulnerableUserAuthority canonicalTraumaClinicalGovernanceBoundary ≡ false
canonicalVulnerableUserAuthorityIsFalse =
  vulnerableUserAuthorityIsFalse canonicalTraumaClinicalGovernanceBoundary

canonicalConsentGateRequiredIsTrue :
  consentGateRequired canonicalTraumaClinicalGovernanceBoundary ≡ true
canonicalConsentGateRequiredIsTrue =
  consentGateRequiredIsTrue canonicalTraumaClinicalGovernanceBoundary

canonicalPacingGateRequiredIsTrue :
  pacingGateRequired canonicalTraumaClinicalGovernanceBoundary ≡ true
canonicalPacingGateRequiredIsTrue =
  pacingGateRequiredIsTrue canonicalTraumaClinicalGovernanceBoundary

canonicalReviewGateRequiredIsTrue :
  reviewGateRequired canonicalTraumaClinicalGovernanceBoundary ≡ true
canonicalReviewGateRequiredIsTrue =
  reviewGateRequiredIsTrue canonicalTraumaClinicalGovernanceBoundary
