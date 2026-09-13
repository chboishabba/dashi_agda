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

exampleInputDoesNotBecomePaperPrediction :
  ExampleInputEqualsPaperPrediction → ⊥
exampleInputDoesNotBecomePaperPrediction ()

desiConditionedFitDoesNotBecomeHeldOutPrediction :
  DESIConditionedFitEqualsHeldOutPrediction → ⊥
desiConditionedFitDoesNotBecomeHeldOutPrediction ()

ambiguousBestFitRowDoesNotPayIndependentManifest :
  AmbiguousBestFitRowPaysIndependentManifest → ⊥
ambiguousBestFitRowDoesNotPayIndependentManifest ()

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
