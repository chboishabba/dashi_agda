module DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinasePDBCVScriptManifestExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinasePhysicalAttributionCoordinatesExact as Coordinates

------------------------------------------------------------------------
-- EXECUTABLE PDB -> CV RECEIPT MANIFEST
--
-- `scripts/adk_pdb_cv_fixture.py` is the deterministic acquisition/evaluation
-- bridge for concrete PDB coordinate manifestations.  It is not the scientific
-- authority for the CV definitions and it is not an Agda proof oracle.
--
-- The script consumes exact PDB bytes plus explicit model/chain/altloc policy,
-- computes the source-defined theta1/theta2 backbone-COM observables, reports
-- two evaluator conventions for the source-underresolved dLN atom subset, and
-- emits a content-addressed JSON evidence packet.
------------------------------------------------------------------------

scriptPath : String
scriptPath = "scripts/adk_pdb_cv_fixture.py"

scriptVersion : String
scriptVersion = "0.1.0"

artifactSchema : String
artifactSchema = "dashi.adk.pdb_cv_fixture.v1"

regressionPath : String
regressionPath = "scripts/test_adk_pdb_cv_fixture.py"

liLiuJiCoordinate = Coordinates.liLiuJiArticleCoordinate
open4AKECoordinate = Coordinates.open4AKECoordinate
closed1AKECoordinate = Coordinates.closed1AKECoordinate
atomicMassCoordinate = Coordinates.atomicMassCoordinate

record PDBCVScriptInputPolicy : Set where
  constructor pdb-cv-script-input-policy
  field
    sourceBytesSha256Required : Bool
    modelSelectionExplicit : Bool
    chainSelectionExplicit : Bool
    alternateLocationPolicyExplicit : Bool
    expectedPdbIdentityMayBeAttached : Bool
    malformedSelectedCoordinateFailsClosed : Bool
    emptySelectedChainFailsClosed : Bool
open PDBCVScriptInputPolicy public

canonicalPDBCVScriptInputPolicy : PDBCVScriptInputPolicy
canonicalPDBCVScriptInputPolicy = pdb-cv-script-input-policy
  true true true true true true true

record PDBCVSelectionManifestPolicy : Set where
  constructor pdb-cv-selection-manifest-policy
  field
    thetaOneLidManifestHashed : Bool
    thetaHingeManifestHashed : Bool
    thetaCoreManifestHashed : Bool
    thetaTwoNmpManifestHashed : Bool
    dLnLidBackboneManifestHashed : Bool
    dLnNmpBackboneManifestHashed : Bool
    dLnLidHeavyManifestHashed : Bool
    dLnNmpHeavyManifestHashed : Bool
    manifestCountRetained : Bool
open PDBCVSelectionManifestPolicy public

canonicalPDBCVSelectionManifestPolicy : PDBCVSelectionManifestPolicy
canonicalPDBCVSelectionManifestPolicy = pdb-cv-selection-manifest-policy
  true true true true true true true true true

record PDBCVEvaluatorSemantics : Set where
  constructor pdb-cv-evaluator-semantics
  field
    thetaOneAtomPolicy : String
    thetaTwoAtomPolicy : String
    dLnBackboneConvention : String
    dLnHeavyConvention : String
    dLnSourceAtomSubsetResolved : Bool
    massConventionReference : String
    floatingPointAcosUsedExternally : Bool
    exactAgdaAcosClaimed : Bool
open PDBCVEvaluatorSemantics public

canonicalPDBCVEvaluatorSemantics : PDBCVEvaluatorSemantics
canonicalPDBCVEvaluatorSemantics = pdb-cv-evaluator-semantics
  "source-paid backbone atoms over the typed theta1 residue groups"
  "source-paid backbone atoms over the typed theta2 residue groups"
  "evaluator convention: backbone atoms over source-paid LID/NMP domain residue ranges"
  "evaluator convention: all non-hydrogen atoms over source-paid LID/NMP domain residue ranges"
  false
  "Prohaska et al. standard/abridged atomic-weight convention; DOI 10.1515/pac-2019-0603"
  true
  false

record PDBCVExecutableReceiptShape : Set where
  constructor pdb-cv-executable-receipt-shape
  field
    artifactSchema : String
    scriptVersion : String
    sourceSha256 : String
    sourceByteCountReading : String
    pdbIdentityReading : String
    modelReading : String
    chainReading : String
    altlocPolicyReading : String
    selectionManifestReference : String
    thetaOneReading : String
    thetaTwoReading : String
    dLnBackboneReading : String
    dLnHeavyReading : String
    promotionBoundary : String
    executionLogReference : String
    executionObserved : Bool
open PDBCVExecutableReceiptShape public

unexecuted4AKETemplate : PDBCVExecutableReceiptShape
unexecuted4AKETemplate = pdb-cv-executable-receipt-shape
  artifactSchema scriptVersion
  "unpaid until exact 4AKE bytes are materialized"
  "unpaid"
  "PDB 4AKE / deposition DOI 10.2210/pdb4AKE/pdb"
  "must be explicit"
  "must be explicit; entry identity alone does not select A or B"
  "blank-or-A currently implemented; must be recorded"
  "unpaid until execution"
  "unexecuted" "unexecuted" "unexecuted" "unexecuted"
  "coordinate-derived executable receipt only; evaluator conventions do not become source-paid and execution does not create formal/scientific authority"
  "no real 4AKE execution receipt in this tranche"
  false

unexecuted1AKETemplate : PDBCVExecutableReceiptShape
unexecuted1AKETemplate = pdb-cv-executable-receipt-shape
  artifactSchema scriptVersion
  "unpaid until exact 1AKE bytes are materialized"
  "unpaid"
  "PDB 1AKE / deposition DOI 10.2210/pdb1AKE/pdb"
  "must be explicit"
  "must be explicit; entry identity alone does not select A or B"
  "blank-or-A currently implemented; must be recorded"
  "unpaid until execution"
  "unexecuted" "unexecuted" "unexecuted" "unexecuted"
  "coordinate-derived executable receipt only; evaluator conventions do not become source-paid and execution does not create formal/scientific authority"
  "no real 1AKE execution receipt in this tranche"
  false

------------------------------------------------------------------------
-- WrongType / attribution firewalls.
------------------------------------------------------------------------

data ScriptExecutionCreatesScientificAuthority : Set where
data ScriptHashCreatesPDBIdentity : Set where
data EvaluatorConventionBecomesSourceDefinition : Set where
data FloatAgreementCreatesExactAgdaTheorem : Set where

data SamePDBIdCreatesSameCoordinateBytes : Set where

scriptExecutionDoesNotCreateScientificAuthority :
  ScriptExecutionCreatesScientificAuthority → ⊥
scriptExecutionDoesNotCreateScientificAuthority ()

scriptHashDoesNotCreatePdbIdentity : ScriptHashCreatesPDBIdentity → ⊥
scriptHashDoesNotCreatePdbIdentity ()

evaluatorConventionDoesNotBecomeSourceDefinition :
  EvaluatorConventionBecomesSourceDefinition → ⊥
evaluatorConventionDoesNotBecomeSourceDefinition ()

floatAgreementDoesNotCreateExactAgdaTheorem : FloatAgreementCreatesExactAgdaTheorem → ⊥
floatAgreementDoesNotCreateExactAgdaTheorem ()

samePdbIdDoesNotCreateSameBytes : SamePDBIdCreatesSameCoordinateBytes → ⊥
samePdbIdDoesNotCreateSameBytes ()

record AdKPDBCVScriptManifestBoundary : Set where
  constructor adk-pdb-cv-script-manifest-boundary
  field
    deterministicArtifactSchemaDefined : Bool
    sourceBytesSha256Required : Bool
    modelChainAltlocPolicyExplicit : Bool
    selectionManifestHashesRequired : Bool
    thetaSourceBackboneDefinitionRetained : Bool
    dLnSourceAtomSubsetResolvedByScript : Bool
    dLnEvaluatorConventionsRemainDistinct : Bool
    massConventionAttributed : Bool
    scriptExecutionCreatesScientificAuthority : Bool
    floatAgreementCreatesExactAgdaTheorem : Bool
    real4AKE1AKEExecutionPaidHere : Bool
open AdKPDBCVScriptManifestBoundary public

canonicalAdKPDBCVScriptManifestBoundary : AdKPDBCVScriptManifestBoundary
canonicalAdKPDBCVScriptManifestBoundary =
  adk-pdb-cv-script-manifest-boundary
    true true true true true false true true
    false false false
