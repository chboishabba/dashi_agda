module DASHI.Physics.Closure.HEPDataEmpiricalSourceCandidateDiagnostic where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Setω)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.DashiDynamicsShiftInstance as DDSI
import DASHI.Physics.Closure.EmpiricalCalibrationBridgeToyFitRealDatasetRouteDiagnostic as C3
import DASHI.Physics.Closure.PhotonuclearEmpiricalEvidenceSummary as Evidence
import DASHI.Physics.Closure.PhotonuclearEmpiricalValidationSummary as Validation

------------------------------------------------------------------------
-- HEPData empirical-source candidate diagnostic.
--
-- Local docs and scripts already contain a HEPData/MeasurementSurface lane.
-- That narrows the empirical blocker: the repo is not missing candidate data
-- surfaces, but it is still missing the accepted projection/authority receipt
-- that would turn those surfaces into a theorem-side empirical bridge.

data HEPDataSourceCandidate : Set where
  canonicalArtifactSchema :
    HEPDataSourceCandidate
  adapterAndConsumerScripts :
    HEPDataSourceCandidate
  programSurfaceScript :
    HEPDataSourceCandidate
  projectionContractStub :
    HEPDataSourceCandidate
  bridgeAndTransformTests :
    HEPDataSourceCandidate
  photonuclearRegistryDocs :
    HEPDataSourceCandidate
  dashifineSiblingArtifacts :
    HEPDataSourceCandidate
  dashiQAuthorityDiscoveryScripts :
    HEPDataSourceCandidate
  dashiQProjectionContractDocs :
    HEPDataSourceCandidate
  dashitestCopiedExperimentalSurfaces :
    HEPDataSourceCandidate
  itirGenericProvenanceScaffold :
    HEPDataSourceCandidate
  itirSiblingSearchSurface :
    HEPDataSourceCandidate

canonicalHEPDataSourceCandidates :
  List HEPDataSourceCandidate
canonicalHEPDataSourceCandidates =
  canonicalArtifactSchema
  ∷ adapterAndConsumerScripts
  ∷ programSurfaceScript
  ∷ projectionContractStub
  ∷ bridgeAndTransformTests
  ∷ photonuclearRegistryDocs
  ∷ dashifineSiblingArtifacts
  ∷ dashiQAuthorityDiscoveryScripts
  ∷ dashiQProjectionContractDocs
  ∷ dashitestCopiedExperimentalSurfaces
  ∷ itirGenericProvenanceScaffold
  ∷ itirSiblingSearchSurface
  ∷ []

data HEPDataCandidateStatus : Set where
  sourceCandidatesPresentButNonPromoting :
    HEPDataCandidateStatus

data HEPDataBridgeMissingSurface : Set where
  missingNamedPhysicalObservableSelection :
    HEPDataBridgeMissingSurface
  missingHEPDataTableColumnSelection :
    HEPDataBridgeMissingSurface
  missingUnitAndDimensionCarrier :
    HEPDataBridgeMissingSurface
  missingCalibrationMapToMeasuredQuantity :
    HEPDataBridgeMissingSurface
  missingComparisonLaw :
    HEPDataBridgeMissingSurface
  missingMeasurementSurfaceToDashiStateProjection :
    HEPDataBridgeMissingSurface
  missingProjectionMetricPropagationLaw :
    HEPDataBridgeMissingSurface
  missingHEPDataObservableSchema :
    HEPDataBridgeMissingSurface
  missingLocalDatasetChecksum :
    HEPDataBridgeMissingSurface
  missingGoldenConformanceTests :
    HEPDataBridgeMissingSurface
  missingHEPDataToITIRAuthorityAdapter :
    HEPDataBridgeMissingSurface
  missingAcceptedDatasetAuthorityToken :
    HEPDataBridgeMissingSurface
  missingW3AcceptedAuthorityReceipt :
    HEPDataBridgeMissingSurface
  missingW8OriginPromotionReceipt :
    HEPDataBridgeMissingSurface

canonicalHEPDataBridgeMissingSurfaces :
  List HEPDataBridgeMissingSurface
canonicalHEPDataBridgeMissingSurfaces =
  missingNamedPhysicalObservableSelection
  ∷ missingHEPDataTableColumnSelection
  ∷ missingUnitAndDimensionCarrier
  ∷ missingCalibrationMapToMeasuredQuantity
  ∷ missingComparisonLaw
  ∷ missingMeasurementSurfaceToDashiStateProjection
  ∷ missingProjectionMetricPropagationLaw
  ∷ missingHEPDataObservableSchema
  ∷ missingLocalDatasetChecksum
  ∷ missingGoldenConformanceTests
  ∷ missingHEPDataToITIRAuthorityAdapter
  ∷ missingAcceptedDatasetAuthorityToken
  ∷ missingW3AcceptedAuthorityReceipt
  ∷ missingW8OriginPromotionReceipt
  ∷ []

record HEPDataEmpiricalSourceCandidateDiagnostic : Setω where
  field
    sourceCandidates :
      List HEPDataSourceCandidate

    sourceCandidatesAreCanonical :
      sourceCandidates ≡ canonicalHEPDataSourceCandidates

    candidateStatus :
      HEPDataCandidateStatus

    photonuclearEvidenceSummary :
      Evidence.PhotonuclearEvidenceSummary Nat

    photonuclearValidationSummary :
      Validation.PhotonuclearEmpiricalValidationSummary Nat

    evidenceStillEmpiricalOnly :
      Evidence.PhotonuclearEvidenceSummary.nonClaimBoundary
        photonuclearEvidenceSummary
      ≡
      Evidence.empiricalOnly

    validationStillEmpiricalOnly :
      Validation.PhotonuclearEmpiricalValidationSummary.nonClaimBoundary
        photonuclearValidationSummary
      ≡
      Validation.empiricalOnlyValidation

    realDatasetAuthorityRoute :
      C3.RealDatasetAuthorityCurrentRouteDiagnostic

    realDatasetAuthorityStillBlocked :
      C3.RealDatasetAuthorityCurrentRouteDiagnostic.currentStatus
        realDatasetAuthorityRoute
      ≡
      C3.blockedAwaitingRealDatasetAuthorityReceipts

    missingBridgeSurfaces :
      List HEPDataBridgeMissingSurface

    missingBridgeSurfacesAreCanonical :
      missingBridgeSurfaces ≡ canonicalHEPDataBridgeMissingSurfaces

    sourcePaths :
      List String

    nextWorkerLanes :
      List String

    nonPromotionBoundary :
      List String

canonicalHEPDataEmpiricalSourceCandidateDiagnostic :
  HEPDataEmpiricalSourceCandidateDiagnostic
canonicalHEPDataEmpiricalSourceCandidateDiagnostic =
  record
    { sourceCandidates =
        canonicalHEPDataSourceCandidates
    ; sourceCandidatesAreCanonical =
        refl
    ; candidateStatus =
        sourceCandidatesPresentButNonPromoting
    ; photonuclearEvidenceSummary =
        DDSI.photonuclearEvidenceSummaryNat
    ; photonuclearValidationSummary =
        DDSI.photonuclearValidationSummaryNat
    ; evidenceStillEmpiricalOnly =
        refl
    ; validationStillEmpiricalOnly =
        refl
    ; realDatasetAuthorityRoute =
        C3.canonicalRealDatasetAuthorityCurrentRouteDiagnostic
    ; realDatasetAuthorityStillBlocked =
        refl
    ; missingBridgeSurfaces =
        canonicalHEPDataBridgeMissingSurfaces
    ; missingBridgeSurfacesAreCanonical =
        refl
    ; sourcePaths =
        "scripts/hepdata_artifact_schema.json"
        ∷ "scripts/hepdata_adapter.py"
        ∷ "scripts/hepdata_consumer.py"
        ∷ "scripts/hepdata_program_surface.py"
        ∷ "scripts/hepdata_projection_contract.py"
        ∷ "tests/test_hepdata_bridge.py"
        ∷ "tests/test_hepdata_transform_validator.py"
        ∷ "Docs/PhotonuclearEmpiricalRegistry.md"
        ∷ "Docs/MeasurementSurfaceProjectionContract.md"
        ∷ "../dashifine/hepdata_npz"
        ∷ "../dashifine/hepdata_npz_all"
        ∷ "../dashifine/26_hepdata.py"
        ∷ "../dashifine/26_hepdata4.py"
        ∷ "../dashifine/26_hepdata_BCD_iterated_contraction_dashi_native.py"
        ∷ "../dashifine/hepdata_to_dashi"
        ∷ "../dashifine/hepdata_to_dashi_all"
        ∷ "../dashifine/hepdata_to_dashi_new"
        ∷ "../dashifine/hepdata_dashi_native"
        ∷ "../dashifine/hepdata_iter_contract"
        ∷ "../dashifine/hepdata_BCD"
        ∷ "../dashifine/hepdata_mdl_fejer_out"
        ∷ "../dashifine/hepdata_seams_out"
        ∷ "../dashifine/hepdata_lyapunov_test_out_new"
        ∷ "../dashifine/hepdata_proof_dossier"
        ∷ "../dashiQ/13tev.py"
        ∷ "../dashiQ/resolve_hepdata_record.py"
        ∷ "../dashiQ/reusable_query.py"
        ∷ "../dashiQ/METHODS.md"
        ∷ "../dashiQ/QUANTUM_BRIDGE_INTERFACE.md"
        ∷ "../dashitest/dashifine"
        ∷ "../dashiQ/temp_dashifine_quantum"
        ∷ "../ITIR-suite/SensibLaw/src/sources/normalized_source.py"
        ∷ "../ITIR-suite/SensibLaw/src/reporting/source_identity.py"
        ∷ "../ITIR-suite/SensibLaw/src/policy/suite_normalized_artifact.py"
        ∷ "../dashifine/*hepdata*"
        ∷ "../ITIR-suite"
        ∷ []
    ; nextWorkerLanes =
        "HEP-A: define HEPDataObservable schema with record/table/citation/units/binning/covariance/checksum"
        ∷ "HEP-B: select one named physical observable and HEPData table column"
        ∷ "HEP-C: define unit/dimension carrier and calibration map"
        ∷ "HEP-D: implement MeasurementSurface -> DashiState projection contract or typed rejection"
        ∷ "HEP-E: construct comparison law and accepted dataset-authority route"
        ∷ "HEP-F: bind HEPData artifact into ITIR normalized-source/provenance scaffold"
        ∷ []
    ; nonPromotionBoundary =
        "HEPData source candidates are present locally, but no theorem-side empirical compatibility is promoted here"
        ∷ "The current MeasurementSurface lane remains packaging-side and empirical-only"
        ∷ "The projection contract explicitly lacks a MeasurementSurface -> DashiState implementation"
        ∷ "The Option C provider attempt remains blocked on accepted authority and W8 origin-promotion receipts"
        ∷ []
    }
