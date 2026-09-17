module DASHI.Wikimedia.JmdLeanIntegratedMachineLineageExact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Wikimedia.AristotleLeanMachineAttributionExact as Archive

------------------------------------------------------------------------
-- ARCHIVE -> INTEGRATED REPOSITORY -> EXECUTION LINEAGE
--
-- The two Aristotle/JMD archives are now integrated into the canonical
-- dashi_lean4 main generation at commit 349f9b7d....  This owner preserves
-- the original archive attribution/digest while giving downstream BIDI
-- receipts a concrete repository-generation identity.
--
-- Integration is not execution: the root Lake graph declares AgdaVendor,
-- AgdaCheck and the wikidata executable, while its ordinary default targets
-- remain Synthesis and Cuisine.  No build/kernel receipt is manufactured by
-- this source owner.
------------------------------------------------------------------------

jmdIntegratedRepository : String
jmdIntegratedRepository = "chboishabba/dashi_lean4"

jmdIntegratedCommit : String
jmdIntegratedCommit = "349f9b7dd49a7f23bfbd7d9da60416afa5440ccf"

jmdIntegratedCommitURL : String
jmdIntegratedCommitURL =
  "https://github.com/chboishabba/dashi_lean4/commit/349f9b7dd49a7f23bfbd7d9da60416afa5440ccf"

jmdIntegratedRoot : String
jmdIntegratedRoot = "DASHI/output-final_aristotle"

jmdIntegratedCommitSource : Source.AttributedSource
jmdIntegratedCommitSource =
  Source.mkNoDOISource
    "JMD (meta-introspector)"
    "Integrate Aristotle archives: DASHI↔Lean bridge and verified ontology engine"
    "chboishabba/dashi_lean4 Git integration commit"
    "2026"
    jmdIntegratedCommitURL
    (Source.namedSourceKind "version-controlled executable integration source")
    "repository-generation identity linking the attributed Aristotle/JMD archive provenance to the canonical dashi_lean4 executable source tree; not an execution receipt, world-truth receipt, Agda proof, or semantic authority"
    Source.publicAttribution

record JmdLeanIntegratedMachine : Set where
  constructor jmd-lean-integrated-machine
  field
    archiveAttribution : Archive.AristotleLeanMachineAttributionReceipt
    archiveSourceRetained : Bool
    repositoryReference : String
    integrationCommitReference : String
    integrationSource : Source.AttributedSource
    integratedSourceRoot : String
    integratedRepositoryIsCanonicalExecutionSurface : Bool
    rootDeclaresAristotleArchive : Bool
    rootDeclaresAgdaVendor : Bool
    rootDeclaresAgdaCheck : Bool
    rootDeclaresWikidataExecutable : Bool
    rootDefaultBuildIncludesAgdaVendor : Bool
    rootDefaultBuildIncludesAgdaCheck : Bool
    rootDefaultBuildIncludesWikidataExecutable : Bool
    integrationCreatesWorldTruth : Bool
    integrationCreatesSemanticAuthority : Bool
    integrationCreatesAgdaProof : Bool

open JmdLeanIntegratedMachine public

canonicalJmdLeanIntegratedMachine : JmdLeanIntegratedMachine
canonicalJmdLeanIntegratedMachine =
  jmd-lean-integrated-machine
    Archive.jmdLeanArchiveAttributionReceipt
    true
    jmdIntegratedRepository
    jmdIntegratedCommit
    jmdIntegratedCommitSource
    jmdIntegratedRoot
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

------------------------------------------------------------------------
-- Concrete declaration binding at the integrated repository generation.
------------------------------------------------------------------------

record IntegratedDeclarationBinding : Set where
  constructor integrated-declaration-binding
  field
    archiveDeclaration : String
    integratedModule : String
    integratedSourceRootReference : String
    integratedCommitReference : String
    declarationPresentInIntegratedSource : Bool
    declarationPresenceIsExecutionReceipt : Bool
    declarationPresenceImportsProofToAgda : Bool

open IntegratedDeclarationBinding public

mkIntegratedDeclarationBinding : String → String → IntegratedDeclarationBinding
mkIntegratedDeclarationBinding declaration moduleName =
  integrated-declaration-binding
    declaration
    moduleName
    jmdIntegratedRoot
    jmdIntegratedCommit
    true
    false
    false

entityDataUrlIntegrated : IntegratedDeclarationBinding
entityDataUrlIntegrated =
  mkIntegratedDeclarationBinding "entityDataUrl" "RequestProject.Cli.Fetch"

fetchEntityJsonIntegrated : IntegratedDeclarationBinding
fetchEntityJsonIntegrated =
  mkIntegratedDeclarationBinding "fetchEntityJson" "RequestProject.Cli.Fetch"

fetchEntityIntegrated : IntegratedDeclarationBinding
fetchEntityIntegrated =
  mkIntegratedDeclarationBinding "fetchEntity" "RequestProject.Cli.Fetch"

scanArticleIntegrated : IntegratedDeclarationBinding
scanArticleIntegrated =
  mkIntegratedDeclarationBinding "scanArticle" "RequestProject.Cli.Enrich"

cmdEnrichIntegrated : IntegratedDeclarationBinding
cmdEnrichIntegrated =
  mkIntegratedDeclarationBinding "cmdEnrich" "RequestProject.Cli.EnrichCmd"

cmdLeanIntegrated : IntegratedDeclarationBinding
cmdLeanIntegrated =
  mkIntegratedDeclarationBinding "cmdLean" "RequestProject.Cli.Tool"

checkSubChainSoundIntegrated : IntegratedDeclarationBinding
checkSubChainSoundIntegrated =
  mkIntegratedDeclarationBinding "checkSubChain_sound" "RequestProject.Cli.Derive"

csvOfRowsIntegrated : IntegratedDeclarationBinding
csvOfRowsIntegrated =
  mkIntegratedDeclarationBinding "csvOfRows / parseCsvText_csvOfRows" "RequestProject.Reports"

worklistCsvIntegrated : IntegratedDeclarationBinding
worklistCsvIntegrated =
  mkIntegratedDeclarationBinding "worklistCsv / parseCsvText_worklistCsv" "RequestProject.Worklist"

------------------------------------------------------------------------
-- Execution is a later receipt, never inferred from repository inclusion.
------------------------------------------------------------------------

data ExecutionResult : Set where
  executionNotObserved : ExecutionResult
  executionPassed : ExecutionResult
  executionFailed : ExecutionResult
  executionBlocked : ExecutionResult

record JmdLeanMachineExecutionReceipt : Set where
  constructor jmd-lean-machine-execution-receipt
  field
    machine : JmdLeanIntegratedMachine
    executionCommitReference : String
    targetReference : String
    toolchainReference : String
    executionResult : ExecutionResult
    executionObserved : Bool
    executionCreatesWorldTruth : Bool
    executionCreatesSemanticAuthority : Bool
    executionCreatesAgdaProof : Bool

open JmdLeanMachineExecutionReceipt public

canonicalJmdLeanMachineExecutionStatus : JmdLeanMachineExecutionReceipt
canonicalJmdLeanMachineExecutionStatus =
  jmd-lean-machine-execution-receipt
    canonicalJmdLeanIntegratedMachine
    jmdIntegratedCommit
    "AgdaVendor / AgdaCheck / AristotleArchive / wikidata explicit target execution"
    "Lean v4.28.0 / mathlib v4.28.0"
    executionNotObserved
    false
    false
    false
    false

------------------------------------------------------------------------
-- Non-collapse firewalls.
------------------------------------------------------------------------

data ArchiveSourceIdentityEqualsIntegratedRepositoryIdentity : Set where
data IntegratedRepositoryIdentityEqualsExecutionReceipt : Set where
data DeclaredLakeTargetEqualsObservedBuild : Set where
data DeclarationPresenceEqualsKernelExecution : Set where

data IntegrationCommitEqualsWorldTruth : Set where

archiveSourceDoesNotEqualIntegratedRepositoryIdentity :
  ArchiveSourceIdentityEqualsIntegratedRepositoryIdentity → ⊥
archiveSourceDoesNotEqualIntegratedRepositoryIdentity ()

integratedRepositoryIdentityDoesNotEqualExecutionReceipt :
  IntegratedRepositoryIdentityEqualsExecutionReceipt → ⊥
integratedRepositoryIdentityDoesNotEqualExecutionReceipt ()

declaredLakeTargetDoesNotEqualObservedBuild :
  DeclaredLakeTargetEqualsObservedBuild → ⊥
declaredLakeTargetDoesNotEqualObservedBuild ()

declarationPresenceDoesNotEqualKernelExecution :
  DeclarationPresenceEqualsKernelExecution → ⊥
declarationPresenceDoesNotEqualKernelExecution ()

integrationCommitDoesNotCreateWorldTruth :
  IntegrationCommitEqualsWorldTruth → ⊥
integrationCommitDoesNotCreateWorldTruth ()

integrationSourceDoesNotImportProof :
  Source.citationImportsProof jmdIntegratedCommitSource ≡ false
integrationSourceDoesNotImportProof =
  Source.citationImportsProofIsFalse jmdIntegratedCommitSource

integrationSourceDoesNotCreateAuthority :
  Source.citationCreatesAuthority jmdIntegratedCommitSource ≡ false
integrationSourceDoesNotCreateAuthority =
  Source.citationCreatesAuthorityIsFalse jmdIntegratedCommitSource
