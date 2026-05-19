module DASHI.Physics.Closure.PhotonuclearEmpiricalValidationSummary where

-- Photonuclear / LHC empirical validation summary.
--
-- This is the smallest repo-facing validation owner for the empirical lane:
-- it wraps the evidence summary, exposes simple counts and status tags, and
-- keeps the boundary explicit that this is still empirical packaging rather
-- than a physics claim.

open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; []; _∷_)

open import DASHI.Physics.Closure.PhotonuclearEmpiricalConstantsRegistry as PECR
open import DASHI.Physics.Closure.PhotonuclearEmpiricalEvidenceSummary as PES
open import DASHI.Physics.Closure.PhotonuclearEmpiricalMeasurementSurface as PEMS

------------------------------------------------------------------------
-- Validation status tags

data ValidationStatus : Set where
  evidenceSummaryRecorded : ValidationStatus
  registryValidated : ValidationStatus
  measurementSurfaceValidated : ValidationStatus
  provenanceValidated : ValidationStatus
  claimBoundaryValidated : ValidationStatus
  empiricalOnlyValidation : ValidationStatus

validationStatusCount : List ValidationStatus → Nat
validationStatusCount [] = zero
validationStatusCount (_ ∷ xs) = suc (validationStatusCount xs)

------------------------------------------------------------------------
-- Counts

record PhotonuclearValidationCounts : Set where
  field
    constantEntries : Nat
    samples : Nat
    measurements : Nat
    provenanceHooks : Nat
    claimLedgerEntries : Nat
    validationStatuses : Nat

mkPhotonuclearValidationCounts :
  ∀ {V : Set} →
  PES.PhotonuclearEvidenceSummary V →
  List ValidationStatus →
  PhotonuclearValidationCounts
mkPhotonuclearValidationCounts evidenceSummary statuses =
  record
    { constantEntries =
        PECR.registryEntryCount
          (PES.PhotonuclearEvidenceSummary.registry evidenceSummary)
    ; samples =
        PEMS.surfaceSampleCount
          (PES.PhotonuclearEvidenceSummary.measurementSurface evidenceSummary)
    ; measurements =
        PEMS.surfaceMeasurementCount
          (PES.PhotonuclearEvidenceSummary.measurementSurface evidenceSummary)
    ; provenanceHooks =
        PEMS.surfaceProvenanceCount
          (PES.PhotonuclearEvidenceSummary.measurementSurface evidenceSummary)
    ; claimLedgerEntries =
        PEMS.surfaceClaimCount
          (PES.PhotonuclearEvidenceSummary.measurementSurface evidenceSummary)
    ; validationStatuses = validationStatusCount statuses
    }

------------------------------------------------------------------------
-- Validation summary

record PhotonuclearEmpiricalValidationSummary (V : Set) : Set₁ where
  field
    validationLabel : String
    evidenceSummary : PES.PhotonuclearEvidenceSummary V
    counts : PhotonuclearValidationCounts
    statuses : List ValidationStatus
    nonClaimBoundary : ValidationStatus

mkPhotonuclearEmpiricalValidationSummary :
  ∀ {V : Set} →
  String →
  PES.PhotonuclearEvidenceSummary V →
  PhotonuclearEmpiricalValidationSummary V
mkPhotonuclearEmpiricalValidationSummary validationLabel evidenceSummary =
  record
    { validationLabel = validationLabel
    ; evidenceSummary = evidenceSummary
    ; counts =
        mkPhotonuclearValidationCounts evidenceSummary
          ( evidenceSummaryRecorded
          ∷ registryValidated
          ∷ measurementSurfaceValidated
          ∷ provenanceValidated
          ∷ claimBoundaryValidated
          ∷ empiricalOnlyValidation
          ∷ []
          )
    ; statuses =
        evidenceSummaryRecorded
        ∷ registryValidated
        ∷ measurementSurfaceValidated
        ∷ provenanceValidated
        ∷ claimBoundaryValidated
        ∷ empiricalOnlyValidation
        ∷ []
    ; nonClaimBoundary = empiricalOnlyValidation
    }
