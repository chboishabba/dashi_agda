module DASHI.Biology.Protein.AdenylateKinaseSituatedProteinWitnessExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.QueryIndexedProjectionAdequacyExact as Query
import DASHI.Biology.Protein.ProteinSituatedHyperfabricExact as Situated
import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseConformationalEmpiricalExact as AdK
import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseStructuralIdentitySnowballExact as Source

------------------------------------------------------------------------
-- ADENYLATE-KINASE INSTANCE OF THE GENERIC SITUATED-PROTEIN QUERY WITNESS.
--
-- The existing 4AKE/1AKE owner pays the same-sequence / distinct-conformation
-- collision.  This adapter does not add a new biological claim or new numeric
-- calibration.  It only exposes that paid collision through the generic
-- situated-protein query interface.
------------------------------------------------------------------------

data ConformationQuery : Set where
  resolvedConformationQuery : ConformationQuery

conformationAnswer : ConformationQuery → AdK.AdKResolvedState → AdK.AdKConformation
conformationAnswer resolvedConformationQuery state = AdK.conformation state

conformationSemantics :
  Query.QuerySemantics AdK.AdKResolvedState ConformationQuery AdK.AdKConformation
conformationSemantics = Query.querySemantics conformationAnswer

sequenceProjectionDefect :
  Query.QueryAdequacyDefect
    AdK.primarySequence
    conformationSemantics
    resolvedConformationQuery
sequenceProjectionDefect =
  Query.queryAdequacyDefect
    AdK.pdb4AKEState
    AdK.pdb1AKEState
    AdK.samePrimarySequence
    AdK.conformationsDiffer

adkSituatedQueryWitness : Situated.SituatedProteinQueryWitness
adkSituatedQueryWitness = Situated.situated-protein-query-witness
  AdK.AdKResolvedState
  AdK.AdKPrimarySequence
  ConformationQuery
  AdK.AdKConformation
  AdK.primarySequence
  conformationSemantics
  resolvedConformationQuery
  sequenceProjectionDefect
  Situated.contextual
  "environment/ligand context separates the two resolved conformations while primary-sequence identity is retained in the finite empirical fixture"
  "4AKE/1AKE PDB depositions and their primary structural literature own the bounded same-polypeptide open/closed structural observations; PDB DOI, UniProt and QID coordinates retain identity/provenance only"
  "DASHI owns the query-indexed situated-protein wrapper and the structural reuse of the paid collision; no AdK source is attributed with the generic theorem"

sequenceNotAdequateForConformationQuery :
  Query.AdequateFor AdK.primarySequence conformationSemantics resolvedConformationQuery → ⊥
sequenceNotAdequateForConformationQuery =
  Situated.witnessBlocksCoarseAdequacy adkSituatedQueryWitness

environmentRepair = AdK.environmentPaysFixture
structuralIdentityBoundary = Source.canonicalAdKStructuralIdentitySnowballBoundary

------------------------------------------------------------------------
-- Cross-domain firewalls.
------------------------------------------------------------------------

data AdKResultCreatesTRPA1Mechanism : Set where
data SameSequenceCreatesUniversalConformationLaw : Set where
data PdbOrQidCreatesDynamicsAuthority : Set where

adkDoesNotCreateTRPA1Mechanism : AdKResultCreatesTRPA1Mechanism → ⊥
adkDoesNotCreateTRPA1Mechanism ()

sameSequenceDoesNotCreateUniversalConformationLaw : SameSequenceCreatesUniversalConformationLaw → ⊥
sameSequenceDoesNotCreateUniversalConformationLaw ()

pdbOrQidDoesNotCreateDynamicsAuthority : PdbOrQidCreatesDynamicsAuthority → ⊥
pdbOrQidDoesNotCreateDynamicsAuthority ()

record AdKSituatedBoundary : Set where
  constructor adk-situated-boundary
  field
    usesGenericSituatedWitness : Bool
    sequenceProjectionInadequateForConformationQuery : Bool
    environmentRepairRetained : Bool
    sameSequenceEmpiricalPairRetained : Bool
    pdbDoiUniprotQidRemainProvenanceOnly : Bool
    adkResultCreatesTrpa1Mechanism : Bool
    sameSequenceCreatesUniversalConformationLaw : Bool
    pdbOrQidCreatesDynamicsAuthority : Bool
open AdKSituatedBoundary public

canonicalAdKSituatedBoundary : AdKSituatedBoundary
canonicalAdKSituatedBoundary = adk-situated-boundary
  true true true true true
  false false false
