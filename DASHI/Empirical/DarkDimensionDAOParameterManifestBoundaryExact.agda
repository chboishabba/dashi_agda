module DASHI.Empirical.DarkDimensionDAOParameterManifestBoundaryExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Empirical.GRQuantumPredictionProtocol as Prediction

------------------------------------------------------------------------
-- DAO / DRMD PARAMETER-MANIFEST BOUNDARY
--
-- The pinned DRMD-CLASS repository contains several useful parameter surfaces,
-- but they are not interchangeable evidence objects:
--
--   input/DRMD.ini
--     example / typical input values;
--
--   cobaya/DRMD.yaml
--     an inference configuration that explicitly includes bao.desi_dr2 and is
--     therefore retrospective with respect to the DESI DR2 BAO observation;
--
--   notebooks/DRMD/DRMD.bestfit
--     a concrete best-fit row, but the inspected file/notebook surface does not
--     source-bind that row to the LSS-independent arXiv:2602.23895 target.
--
-- The repository README does source-bind DRMD_v2 to arXiv:2602.23895.  That
-- pays code-version relevance, not the stronger claim that any particular
-- checked-in config/best-fit row is the executable manifest for that paper's
-- LSS-independent posterior.
--
-- The pinned public snapshot used here is dated 2026-06-04, later than the
-- paper submission date 2026-02-27.  A later snapshot can preserve/reproduce
-- the model while still failing to certify which exact parameter manifest was
-- used for the earlier paper inference.
--
-- A future same-key prospective prediction must therefore identify and freeze
-- the actual parameter manifest used for the independent target, and record a
-- parameterManifestHash as required by GRQuantumPredictionProtocol.
------------------------------------------------------------------------

record DAOParameterManifestStatus : Set where
  constructor daoParameterManifestStatus
  field
    exampleInputLocated : Bool
    retrospectiveDESIConfigLocated : Bool
    bestFitRowLocated : Bool
    repositoryVersionLinkedToIndependentTarget : Bool
    pinnedSnapshotPostdatesIndependentPaper : Bool
    snapshotChronologyPaysPaperManifest : Bool
    independentTargetSpecificConfigLocated : Bool
    bestFitRowSourceBoundToIndependentTarget : Bool
    independentTargetExecutableManifestFrozen : Bool
    parameterManifestHashRecorded : Bool
    manifestExecutionPermittedAsPaperPrediction : Bool

open DAOParameterManifestStatus public

canonicalDAOParameterManifestStatus : DAOParameterManifestStatus
canonicalDAOParameterManifestStatus =
  daoParameterManifestStatus
    true
    true
    true
    true
    true
    false
    false
    false
    false
    false
    false

exampleInputPath : String
exampleInputPath = "input/DRMD.ini"

retrospectiveDESIConfigPath : String
retrospectiveDESIConfigPath = "cobaya/DRMD.yaml"

bestFitRowPath : String
bestFitRowPath = "notebooks/DRMD/DRMD.bestfit"

retrospectiveLikelihoodCoordinate : String
retrospectiveLikelihoodCoordinate = "bao.desi_dr2"

independentTargetArXiv : String
independentTargetArXiv = "2602.23895"

independentPaperSubmissionDate : String
independentPaperSubmissionDate = "2026-02-27"

pinnedPublicSnapshotDate : String
pinnedPublicSnapshotDate = "2026-06-04"

------------------------------------------------------------------------
-- Direct weld to the existing prediction-provenance coordinate.
------------------------------------------------------------------------

predictionParameterManifestHash : Prediction.PredictionProvenance → String
predictionParameterManifestHash = Prediction.parameterManifestHash

------------------------------------------------------------------------
-- WrongType firewalls.
------------------------------------------------------------------------

data ExampleInputEqualsPaperPrediction : Set where

data DESIConditionedFitEqualsHeldOutPrediction : Set where

data AmbiguousBestFitRowPaysIndependentManifest : Set where

data VersionLinkManufacturesSpecificConfig : Set where

data LaterSnapshotCertifiesPaperManifest : Set where

exampleInputDoesNotBecomePaperPrediction :
  ExampleInputEqualsPaperPrediction → ⊥
exampleInputDoesNotBecomePaperPrediction ()

desiConditionedFitDoesNotBecomeHeldOutPrediction :
  DESIConditionedFitEqualsHeldOutPrediction → ⊥
desiConditionedFitDoesNotBecomeHeldOutPrediction ()

ambiguousBestFitRowDoesNotPayIndependentManifest :
  AmbiguousBestFitRowPaysIndependentManifest → ⊥
ambiguousBestFitRowDoesNotPayIndependentManifest ()

versionLinkDoesNotManufactureSpecificConfig :
  VersionLinkManufacturesSpecificConfig → ⊥
versionLinkDoesNotManufactureSpecificConfig ()

laterSnapshotDoesNotCertifyPaperManifest :
  LaterSnapshotCertifiesPaperManifest → ⊥
laterSnapshotDoesNotCertifyPaperManifest ()

repositoryVersionLinkPaid :
  repositoryVersionLinkedToIndependentTarget canonicalDAOParameterManifestStatus
  ≡ true
repositoryVersionLinkPaid = refl

pinnedSnapshotChronologyRecorded :
  pinnedSnapshotPostdatesIndependentPaper canonicalDAOParameterManifestStatus
  ≡ true
pinnedSnapshotChronologyRecorded = refl

snapshotChronologyStillNonPromoting :
  snapshotChronologyPaysPaperManifest canonicalDAOParameterManifestStatus
  ≡ false
snapshotChronologyStillNonPromoting = refl

independentTargetConfigStillOpen :
  independentTargetSpecificConfigLocated canonicalDAOParameterManifestStatus
  ≡ false
independentTargetConfigStillOpen = refl

independentTargetManifestStillOpen :
  independentTargetExecutableManifestFrozen canonicalDAOParameterManifestStatus
  ≡ false
independentTargetManifestStillOpen = refl

parameterManifestHashStillOpen :
  parameterManifestHashRecorded canonicalDAOParameterManifestStatus ≡ false
parameterManifestHashStillOpen = refl

paperPredictionExecutionStillBlocked :
  manifestExecutionPermittedAsPaperPrediction canonicalDAOParameterManifestStatus
  ≡ false
paperPredictionExecutionStillBlocked = refl
