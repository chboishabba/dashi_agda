module DASHI.Context.RoleScopedAccessContract where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

open import DASHI.Context.ContextEnvelopeInvariant
open import DASHI.Context.NarrativeProjectionBoundary

------------------------------------------------------------------------
-- Purpose-limited access contract.
--
-- Access is not ownership of the record.  A clinician, advocate,
-- journalist, or public team receives only a scoped projection, while the
-- protected subject retains the canonical context-bearing artifact.


data AccessPurpose : Set where
  personalReview : AccessPurpose
  carePlanning : AccessPurpose
  legalAdvocacy : AccessPurpose
  affidavitPreparation : AccessPurpose
  journalisticVerification : AccessPurpose
  publicAdministrationReview : AccessPurpose

record AccessGrant : Set where
  field
    granteeRole : AudienceRole
    purpose : AccessPurpose
    allowedArtifactIds : List String
    allowedProjectionKinds : List ProjectionKind
    expiresAt : String

    subjectConsent : Bool
    subjectConsentIsTrue : subjectConsent ≡ true

    minimumNecessary : Bool
    minimumNecessaryIsTrue : minimumNecessary ≡ true

    purposeLimited : Bool
    purposeLimitedIsTrue : purposeLimited ≡ true

    exportScoped : Bool
    exportScopedIsTrue : exportScoped ≡ true

    accessLogged : Bool
    accessLoggedIsTrue : accessLogged ≡ true

    revocable : Bool
    revocableIsTrue : revocable ≡ true

open AccessGrant public

record ClinicianContract : Set where
  field
    grant : AccessGrant
    roleIsClinician : granteeRole grant ≡ clinician
    purposeIsCarePlanning : purpose grant ≡ carePlanning

    diagnosisNotInferredFromRecord : Bool
    diagnosisNotInferredFromRecordIsTrue :
      diagnosisNotInferredFromRecord ≡ true

    exposureNotForced : Bool
    exposureNotForcedIsTrue : exposureNotForced ≡ true

    legalExportBlockedByDefault : Bool
    legalExportBlockedByDefaultIsTrue :
      legalExportBlockedByDefault ≡ true

open ClinicianContract public

record AdvocateContract : Set where
  field
    grant : AccessGrant
    roleIsAdvocate : granteeRole grant ≡ advocate
    purposeIsLegalAdvocacy : purpose grant ≡ legalAdvocacy

    clinicalNotesHiddenByDefault : Bool
    clinicalNotesHiddenByDefaultIsTrue :
      clinicalNotesHiddenByDefault ≡ true

    legalConclusionsUserAuthoredOnly : Bool
    legalConclusionsUserAuthoredOnlyIsTrue :
      legalConclusionsUserAuthoredOnly ≡ true

    chronologyMayRemainApproximate : Bool
    chronologyMayRemainApproximateIsTrue :
      chronologyMayRemainApproximate ≡ true

open AdvocateContract public

canonicalClinicianGrant : AccessGrant
canonicalClinicianGrant =
  record
    { granteeRole = clinician
    ; purpose = carePlanning
    ; allowedArtifactIds = []
    ; allowedProjectionKinds = clinicalHandoffView ∷ timelineView ∷ []
    ; expiresAt = "explicitly bounded"
    ; subjectConsent = true
    ; subjectConsentIsTrue = refl
    ; minimumNecessary = true
    ; minimumNecessaryIsTrue = refl
    ; purposeLimited = true
    ; purposeLimitedIsTrue = refl
    ; exportScoped = true
    ; exportScopedIsTrue = refl
    ; accessLogged = true
    ; accessLoggedIsTrue = refl
    ; revocable = true
    ; revocableIsTrue = refl
    }

canonicalClinicianContract : ClinicianContract
canonicalClinicianContract =
  record
    { grant = canonicalClinicianGrant
    ; roleIsClinician = refl
    ; purposeIsCarePlanning = refl
    ; diagnosisNotInferredFromRecord = true
    ; diagnosisNotInferredFromRecordIsTrue = refl
    ; exposureNotForced = true
    ; exposureNotForcedIsTrue = refl
    ; legalExportBlockedByDefault = true
    ; legalExportBlockedByDefaultIsTrue = refl
    }

canonicalAdvocateGrant : AccessGrant
canonicalAdvocateGrant =
  record
    { granteeRole = advocate
    ; purpose = legalAdvocacy
    ; allowedArtifactIds = []
    ; allowedProjectionKinds = advocateChronologyView ∷ evidenceIndexView ∷ affidavitView ∷ []
    ; expiresAt = "explicitly bounded"
    ; subjectConsent = true
    ; subjectConsentIsTrue = refl
    ; minimumNecessary = true
    ; minimumNecessaryIsTrue = refl
    ; purposeLimited = true
    ; purposeLimitedIsTrue = refl
    ; exportScoped = true
    ; exportScopedIsTrue = refl
    ; accessLogged = true
    ; accessLoggedIsTrue = refl
    ; revocable = true
    ; revocableIsTrue = refl
    }

canonicalAdvocateContract : AdvocateContract
canonicalAdvocateContract =
  record
    { grant = canonicalAdvocateGrant
    ; roleIsAdvocate = refl
    ; purposeIsLegalAdvocacy = refl
    ; clinicalNotesHiddenByDefault = true
    ; clinicalNotesHiddenByDefaultIsTrue = refl
    ; legalConclusionsUserAuthoredOnly = true
    ; legalConclusionsUserAuthoredOnlyIsTrue = refl
    ; chronologyMayRemainApproximate = true
    ; chronologyMayRemainApproximateIsTrue = refl
    }
