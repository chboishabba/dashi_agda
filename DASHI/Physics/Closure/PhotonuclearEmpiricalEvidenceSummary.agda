module DASHI.Physics.Closure.PhotonuclearEmpiricalEvidenceSummary where

open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

open import DASHI.Physics.Closure.PhotonuclearEmpiricalConstantsRegistry as PECR
open import DASHI.Physics.Closure.PhotonuclearEmpiricalMeasurementSurface as PEMS

------------------------------------------------------------------------
-- Repo-facing empirical evidence summary for the photonuclear / LHC lane.
--
-- This is a control surface, not a fit or closure theorem. It gathers the
-- current constants registry and measurement surface into one durable module
-- so downstream code and docs can cite:
--   * what constants were registered,
--   * what samples/measurements were packaged,
--   * what provenance hooks exist, and
--   * what non-claim boundary remains in force.

data EvidenceStatus : Set where
  registryRecorded : EvidenceStatus
  measurementsPackaged : EvidenceStatus
  provenanceRecorded : EvidenceStatus
  claimBoundaryRecorded : EvidenceStatus
  empiricalOnly : EvidenceStatus

record PhotonuclearEvidenceCounts : Set where
  field
    constantEntries : Nat
    samples : Nat
    measurements : Nat
    provenanceHooks : Nat
    claimLedgerEntries : Nat

record PhotonuclearEvidenceSummary (V : Set) : Set₁ where
  field
    summaryLabel : String
    registry : PECR.PhotonuclearConstantsRegistry
    measurementSurface : PEMS.PhotonuclearEmpiricalMeasurementSurface V
    counts : PhotonuclearEvidenceCounts
    statuses : List EvidenceStatus
    nonClaimBoundary : EvidenceStatus

mkPhotonuclearEvidenceCounts :
  ∀ {V : Set} →
  PECR.PhotonuclearConstantsRegistry →
  PEMS.PhotonuclearEmpiricalMeasurementSurface V →
  PhotonuclearEvidenceCounts
mkPhotonuclearEvidenceCounts registry surface =
  record
    { constantEntries = PECR.registryEntryCount registry
    ; samples = PEMS.surfaceSampleCount surface
    ; measurements = PEMS.surfaceMeasurementCount surface
    ; provenanceHooks = PEMS.surfaceProvenanceCount surface
    ; claimLedgerEntries = PEMS.surfaceClaimCount surface
    }

mkPhotonuclearEvidenceSummary :
  ∀ {V : Set} →
  String →
  PECR.PhotonuclearConstantsRegistry →
  PEMS.PhotonuclearEmpiricalMeasurementSurface V →
  PhotonuclearEvidenceSummary V
mkPhotonuclearEvidenceSummary summaryLabel registry measurementSurface =
  record
    { summaryLabel = summaryLabel
    ; registry = registry
    ; measurementSurface = measurementSurface
    ; counts = mkPhotonuclearEvidenceCounts registry measurementSurface
    ; statuses =
        registryRecorded
        ∷ measurementsPackaged
        ∷ provenanceRecorded
        ∷ claimBoundaryRecorded
        ∷ empiricalOnly
        ∷ []
    ; nonClaimBoundary = empiricalOnly
    }
