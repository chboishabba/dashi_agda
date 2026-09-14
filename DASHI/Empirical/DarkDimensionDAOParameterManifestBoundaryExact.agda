module DASHI.Empirical.DarkDimensionDAOParameterManifestBoundaryExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Empirical.DarkDimensionDAOPaperTableReconstructionExact as PaperReconstruction
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
--     a concrete best-fit row.  Its interaction-strength coordinate is
--     log10G/(aH)=13.05733, while arXiv:2602.23895 fixes (G/H)_ini=10^7,
--     i.e. log10(G/H)=7.  That directly rules out same-manifest identity.
--
-- The repository README does source-bind DRMD_v2 to arXiv:2602.23895.  That
-- pays code-version relevance, not the stronger claim that any particular
-- checked-in config/best-fit row is the executable manifest for that paper's
-- LSS-independent posterior.
--
-- The paper itself publishes a nearly complete extended-analysis best-fit point
-- in Table I.  DarkDimensionDAOPaperTableReconstructionExact records that point
-- and reconstructs z_stop through the paper's approximate Eq. (13).  This pays
-- a runnable reconstruction packet, but not custody/identity of the authors'
-- original MCMC manifest.
--
-- The pinned public snapshot used here is dated 2026-06-04, later than the
-- paper submission date 2026-02-27.  A later snapshot can preserve/reproduce
-- the model while still failing to certify which exact parameter manifest was
-- used for the earlier paper inference.
--
-- A future exact paper-manifest claim must therefore identify and freeze the
-- actual parameter manifest used for the independent target, and record a
-- parameterManifestHash as required by GRQuantumPredictionProtocol.
------------------------------------------------------------------------

record DAOParameterManifestStatus : Set where
  constructor daoParameterManifestStatus
  field
    exampleInputLocated : Bool
    retrospectiveDESIConfigLocated : Bool
    bestFitRowLocated : Bool
    bestFitRowMatchesPaperFixedInteractionStrength : Bool
    repositoryVersionLinkedToIndependentTarget : Bool
    paperTableReconstructionLocated : Bool
    paperTableReconstructionRunnable : Bool
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
    false
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

publicBestFitLog10InitialInteraction : String
publicBestFitLog10InitialInteraction = "13.05733"

paperFixedLog10InitialInteraction : String
paperFixedLog10InitialInteraction = "7"

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

data PaperTableReconstructionClosesOriginalManifestDebt : Set where

data PublicBestFitIsIndependentPaperBestFit : Set where

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

paperTableReconstructionDoesNotCloseOriginalManifestDebt :
  PaperTableReconstructionClosesOriginalManifestDebt → ⊥
paperTableReconstructionDoesNotCloseOriginalManifestDebt ()

publicBestFitCannotBeIndependentPaperBestFit :
  PublicBestFitIsIndependentPaperBestFit → ⊥
publicBestFitCannotBeIndependentPaperBestFit ()

repositoryVersionLinkPaid :
  repositoryVersionLinkedToIndependentTarget canonicalDAOParameterManifestStatus
  ≡ true
repositoryVersionLinkPaid = refl

publicBestFitInteractionCoordinateMismatchRecorded :
  bestFitRowMatchesPaperFixedInteractionStrength canonicalDAOParameterManifestStatus
  ≡ false
publicBestFitInteractionCoordinateMismatchRecorded = refl

paperTableReconstructionLocatedAndRunnable :
  paperTableReconstructionRunnable canonicalDAOParameterManifestStatus ≡ true
paperTableReconstructionLocatedAndRunnable = refl

sourceReconstructionRunnableWithoutOriginalCustody :
  PaperReconstruction.reconstructionManifestRunnable
    PaperReconstruction.canonicalPaperTableReconstructionStatus
  ≡ true
sourceReconstructionRunnableWithoutOriginalCustody =
  PaperReconstruction.reconstructionCanRunWithoutClaimingOriginalCustody

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
