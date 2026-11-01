module DASHI.Cognition.PNF.SensibLawRuntimeDatabaseConfigurationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- RUNTIME DATABASE CONFIGURATION
--
-- Operational parity target: SLR sensiblaw-pg-source-store.
--
-- Configuration precedence:
--   1. existing process DATABASE_URL;
--   2. explicitly selected env file;
--   3. local .env;
--   4. otherwise configuration residual.
--
-- Configuration is an execution concern only.  It is not source provenance,
-- evidence, semantic state, legal authority, or an acquisition receipt.
------------------------------------------------------------------------

data DatabaseConfigurationSource : Set where
  processEnvironment : DatabaseConfigurationSource
  explicitEnvFile : DatabaseConfigurationSource
  localDotEnv : DatabaseConfigurationSource

data DatabaseConfigurationState : Set where
  databaseConfigured : DatabaseConfigurationState
  databaseConfigurationResidual : DatabaseConfigurationState

record DatabaseConfigurationReceipt : Set where
  constructor database-configuration-receipt
  field
    source : DatabaseConfigurationSource
    databaseURLConfigured : Bool
    secretValueRedacted : Bool
    existingProcessValuePreserved : Bool
    configurationReference : String

open DatabaseConfigurationReceipt public

record DatabaseConfigurationResidualReceipt : Set where
  constructor database-configuration-residual-receipt
  field
    residualReference : String
    sourceAbsenceClaimed : Bool
    negativeLegalEvidenceCreated : Bool
    legalFollowFrontierClosed : Bool

open DatabaseConfigurationResidualReceipt public

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data DatabaseConfigCreatesSourceReceipt : Set where
data DatabaseConfigCreatesLegalAuthority : Set where
data DatabaseConfigCreatesSemanticState : Set where
data DatabaseConfigCreatesAtomicGate : Set where
data MissingDatabaseConfigProvesSourceAbsent : Set where
data EnvFileMayOverrideExistingProcessValue : Set where

databaseConfigDoesNotCreateSourceReceipt : DatabaseConfigCreatesSourceReceipt → ⊥
databaseConfigDoesNotCreateSourceReceipt ()

databaseConfigDoesNotCreateLegalAuthority : DatabaseConfigCreatesLegalAuthority → ⊥
databaseConfigDoesNotCreateLegalAuthority ()

databaseConfigDoesNotCreateSemanticState : DatabaseConfigCreatesSemanticState → ⊥
databaseConfigDoesNotCreateSemanticState ()

databaseConfigDoesNotCreateAtomicGate : DatabaseConfigCreatesAtomicGate → ⊥
databaseConfigDoesNotCreateAtomicGate ()

missingDatabaseConfigDoesNotProveSourceAbsent :
  MissingDatabaseConfigProvesSourceAbsent → ⊥
missingDatabaseConfigDoesNotProveSourceAbsent ()

envFileCannotOverrideExistingProcessValueByPermission :
  EnvFileMayOverrideExistingProcessValue → ⊥
envFileCannotOverrideExistingProcessValueByPermission ()

record RuntimeDatabaseConfigurationBoundary : Set where
  constructor runtime-database-configuration-boundary
  field
    processEnvironmentHasPriority : Bool
    explicitEnvFileSupported : Bool
    localDotEnvSupported : Bool
    secretValuesRedacted : Bool
    existingProcessValuePreserved : Bool
    configCreatesSourceReceipt : Bool
    configCreatesAuthority : Bool
    configCreatesSemanticState : Bool
    missingConfigCreatesNegativeEvidence : Bool

canonicalRuntimeDatabaseConfigurationBoundary : RuntimeDatabaseConfigurationBoundary
canonicalRuntimeDatabaseConfigurationBoundary =
  runtime-database-configuration-boundary
    true true true true true false false false false
