module DASHI.Biology.Protein.TRPA1SituatedProteinWitnessExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.QueryIndexedProjectionAdequacyExact as Query
import DASHI.Biology.Protein.ProteinSituatedHyperfabricExact as Situated
import DASHI.Biology.Protein.TRPA1SingleResidueThermalAdaptationExact as TRPA1
import DASHI.Biology.Protein.TRPA1SourceAttributionEnvelopeExact as Source

------------------------------------------------------------------------
-- TRPA1 INSTANCE OF THE GENERIC SITUATED-PROTEIN QUERY WITNESS.
--
-- Feng et al. own the bounded comparative/mutational biology.  DASHI owns the
-- generic query-indexed factorisation wrapper.  DOI/PMID/PMCID/QID remain
-- provenance coordinates and do not create the thermal-response proposition.
------------------------------------------------------------------------

data ThermalQuery : Set where
  thermalResponseQuery : ThermalQuery

thermalAnswer : ThermalQuery → TRPA1.TRPA1RichState → TRPA1.ThermalResponse
thermalAnswer thermalResponseQuery state = TRPA1.thermalReadout state

thermalSemantics : Query.QuerySemantics TRPA1.TRPA1RichState ThermalQuery TRPA1.ThermalResponse
thermalSemantics = Query.querySemantics thermalAnswer

proteinIdentityDefect :
  Query.QueryAdequacyDefect
    TRPA1.proteinIdentity
    thermalSemantics
    thermalResponseQuery
proteinIdentityDefect =
  Query.queryAdequacyDefect
    TRPA1.ancestralLikeTRPA1
    TRPA1.mammalianAspartateTRPA1
    TRPA1.sameProteinIdentity
    TRPA1.thermalResponseSeparates

trpa1SituatedQueryWitness : Situated.SituatedProteinQueryWitness
trpa1SituatedQueryWitness = situated-protein-query-witness
  TRPA1.TRPA1RichState
  TRPA1.ProteinIdentity
  ThermalQuery
  TRPA1.ThermalResponse
  TRPA1.proteinIdentity
  thermalSemantics
  thermalResponseQuery
  proteinIdentityDefect
  Situated.slowlyVarying
  "pore-residue state separates thermal responses while protein identity is unchanged in the finite source-shaped witness"
  "Feng et al. 2026 owns the bounded residue/gating and intervention propositions; DOI 10.1126/sciadv.aee3948, PMID 42685214, PMCID PMC13537265; article QID remains unresolved"
  "DASHI owns the generic query-indexed non-factorability/situated-protein instantiation; it does not transfer Feng authorship to the generic theorem"

residueAwareRepair = TRPA1.thermalResponseFactorsThroughResidueAware
sourceAttributionBoundary = Source.canonicalTRPA1SourceAttributionBoundary

------------------------------------------------------------------------
-- Cross-domain firewalls.
------------------------------------------------------------------------

data TRPA1ResultCreatesAdKMechanism : Set where
data GenericWitnessCreatesUniversalResidueLaw : Set where

data SourceIdentifiersCreateThermalMechanism : Set where

trpa1DoesNotCreateAdKMechanism : TRPA1ResultCreatesAdKMechanism → ⊥
trpa1DoesNotCreateAdKMechanism ()

genericWitnessDoesNotCreateUniversalResidueLaw : GenericWitnessCreatesUniversalResidueLaw → ⊥
genericWitnessDoesNotCreateUniversalResidueLaw ()

sourceIdentifiersDoNotCreateThermalMechanism : SourceIdentifiersCreateThermalMechanism → ⊥
sourceIdentifiersDoNotCreateThermalMechanism ()

record TRPA1SituatedBoundary : Set where
  constructor trpa1-situated-boundary
  field
    usesGenericSituatedWitness : Bool
    proteinIdentityProjectionInadequateForThermalQuery : Bool
    residueAwareRepairRetained : Bool
    fengSourceRoleRetained : Bool
    doiPmidPmcidRetainedAsProvenance : Bool
    articleQidMayRemainUnresolved : Bool
    genericWitnessCreatesUniversalResidueLaw : Bool
    trpa1ResultCreatesAdkMechanism : Bool
    sourceIdentifiersCreateThermalMechanism : Bool
open TRPA1SituatedBoundary public

canonicalTRPA1SituatedBoundary : TRPA1SituatedBoundary
canonicalTRPA1SituatedBoundary = trpa1-situated-boundary
  true true true true true true
  false false false
