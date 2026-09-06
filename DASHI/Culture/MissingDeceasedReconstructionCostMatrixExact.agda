module DASHI.Culture.MissingDeceasedReconstructionCostMatrixExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
import DASHI.Core.CapabilityReconstructionCostBidiExact as R

maiwaldProjectContinuity : R.ReconstructionCostProfile
maiwaldProjectContinuity = R.reconstruction-cost-profile
  "JPL/JILA action-spectroscopy biosignature project"
  (R.namedSuccessor ∷ R.overlappingTeam ∷ R.duplicateCapability ∷ [])
  [] R.low
  "JPL SURP 2023-2025 project archive; FY24 poster SP23012p; JILA Weber Group project page"
  "Low reconstruction pressure only at the project/team substrate level: Deacon Nemchick succeeds as PI, Hodyss and Weber persist, and the external Weber-group experimental capability remains available. Exact JPL calibration, qualification, notebook, repository, configuration and tacit-transfer continuity is not thereby proved."

hicksEventTimeContinuity : R.ReconstructionCostProfile
hicksEventTimeContinuity = R.reconstruction-cost-profile
  "Michael Hicks JPL small-body science/application workflow"
  [] [] R.unknown
  "AAS DPS and University of Arizona LPL memorials: JPL tenure 1998-2022; death 2023-07-30"
  "No public event-time JPL-role continuity or rebuild/handover receipt has been established for the interval after the 2022 JPL departure."

eskridgeInstituteContinuity : R.ReconstructionCostProfile
eskridgeInstituteContinuity = R.reconstruction-cost-profile
  "Institute for Exotic Science / HoloChron gravity-modification application stack"
  (R.overlappingTeam ∷ []) [] R.unknown
  "HAL5 2018 team/organisation deck and later Institute-boundary evidence"
  "A multi-person team surface exists, but apparatus, notebook, repository, calibration, raw/reduced data, failure history and post-death asset-transfer receipts remain unresolved."

mccaslandOrganizationalContinuity : R.ReconstructionCostProfile
mccaslandOrganizationalContinuity = R.reconstruction-cost-profile
  "ATA/BlueHalo/AeroVironment application-technology portfolio"
  [] [] R.unknown
  "ATA appointment record; BlueHalo formation 2020; AeroVironment acquisition closed 2025-05-01"
  "Organisational continuity exists at company level, but McCasland's exact post-acquisition application portfolio, access-transfer, named successor and technical handover remain unresolved."

loureiroExternalReproducibility : R.ReconstructionCostProfile
loureiroExternalReproducibility = R.reconstruction-cost-profile
  "Reduced-gyrokinetic / Fourier-Hermite numerical application stack"
  (R.documentedProcedure ∷ R.duplicateCapability ∷ []) [] R.moderate
  "Loureiro et al. CPC 206 (2016) DOI 10.1016/j.cpc.2016.05.004; MIT PSFC Viriato description; later open derivative/student implementation evidence"
  "Published equations, architecture and benchmarks plus derivative implementations create external reproducibility pressure. This does not prove transfer of the exact MIT target-specific configuration, source state, closure choices, validation corpus or tacit workflow."

record ReconstructionMatrixBoundary : Set where
  constructor reconstruction-matrix-boundary
  field
    lowProjectCostImpliesLowExactCarrierCost : Bool
    lowProjectCostImpliesLowExactCarrierCostIsFalse : lowProjectCostImpliesLowExactCarrierCost ≡ false
    externalReproducibilityImpliesInternalHandover : Bool
    externalReproducibilityImpliesInternalHandoverIsFalse : externalReproducibilityImpliesInternalHandover ≡ false
    historicalTeamImpliesPostEventAssetTransfer : Bool
    historicalTeamImpliesPostEventAssetTransferIsFalse : historicalTeamImpliesPostEventAssetTransfer ≡ false
    noPublicRebuildReceiptImpliesNoReconstructionCost : Bool
    noPublicRebuildReceiptImpliesNoReconstructionCostIsFalse : noPublicRebuildReceiptImpliesNoReconstructionCost ≡ false

canonicalReconstructionMatrixBoundary : ReconstructionMatrixBoundary
canonicalReconstructionMatrixBoundary = reconstruction-matrix-boundary false refl false refl false refl false refl
