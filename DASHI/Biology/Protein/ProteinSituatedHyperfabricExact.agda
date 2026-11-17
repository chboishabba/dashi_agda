module DASHI.Biology.Protein.ProteinSituatedHyperfabricExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.List using (List)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.QueryIndexedProjectionAdequacyExact as Query
import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Wikimedia.SnowballExternalIdentityAvailabilityExact as Identity
import DASHI.Biology.Protein.ProteinRecoveryBoundary as Recovery

------------------------------------------------------------------------
-- GENERIC SITUATED PROTEIN HYPERFABRIC
--
-- This is a thin composition layer over existing DASHI protein/query/source
-- machinery.  It does not replace ProteinRecoveryBoundary and does not assert a
-- universal biological state ontology.  Its purpose is only to retain the
-- coordinate classes needed for consumer-relative protein observations.
------------------------------------------------------------------------

data CoordinateRole : Set where
  identityStable : CoordinateRole
  slowlyVarying : CoordinateRole
  contextual : CoordinateRole
  fastDynamical : CoordinateRole
  historyDependent : CoordinateRole
  observerDependent : CoordinateRole

record SituatedProteinObserver : Set₁ where
  constructor situated-protein-observer
  field
    assay : String
    samplingWindow : String
    resolution : String
    perturbation : String
    localContext : String
    sourceProvenance : Attribution.AttributedSource
    externalIdentities : List Identity.ExternalIdentityDemand
open SituatedProteinObserver public

record ProteinSituatedHyperfabric : Set₁ where
  constructor protein-situated-hyperfabric
  field
    GenomicState : Set
    TranslationContext : Set
    RealisedProteinState : Set
    EnvironmentState : Set
    MetabolicState : Set
    HistoryState : Set
    ObserverState : Set
    ResidualState : Set
open ProteinSituatedHyperfabric public

record ProteinSituatedPoint (H : ProteinSituatedHyperfabric) : Set where
  constructor protein-situated-point
  field
    genomic : GenomicState H
    translation : TranslationContext H
    realisedProtein : RealisedProteinState H
    environment : EnvironmentState H
    metabolism : MetabolicState H
    history : HistoryState H
    observer : ObserverState H
    residual : ResidualState H
open ProteinSituatedPoint public

AdmissibilityPredicate : ProteinSituatedHyperfabric → Set₁
AdmissibilityPredicate H = ProteinSituatedPoint H → Set

record SituatedProteinAdmissibility (H : ProteinSituatedHyperfabric) : Set₁ where
  constructor situated-protein-admissibility
  field
    admissible : AdmissibilityPredicate H
    interpretation : String
open SituatedProteinAdmissibility public

------------------------------------------------------------------------
-- Common query-witness interface.
--
-- TRPA1 and AdK instantiate this exact record while keeping their state spaces,
-- observations and separating fibres domain-specific.
------------------------------------------------------------------------

record SituatedProteinQueryWitness : Set₁ where
  constructor situated-protein-query-witness
  field
    State : Set
    Observation : Set
    QueryType : Set
    Answer : Set
    project : State → Observation
    semantics : Query.QuerySemantics State QueryType Answer
    query : QueryType
    adequacyDefect : Query.QueryAdequacyDefect project semantics query
    separatingCoordinateRole : CoordinateRole
    separatingCoordinateReading : String
    empiricalSourceRole : String
    dashiFormalisationRole : String
open SituatedProteinQueryWitness public

witnessBlocksCoarseAdequacy :
  (W : SituatedProteinQueryWitness) →
  Query.AdequateFor
    (project W)
    (semantics W)
    (query W) →
  ⊥
witnessBlocksCoarseAdequacy W =
  Query.queryAdequacyDefectBlocksFactorisation (adequacyDefect W)

------------------------------------------------------------------------
-- Reuse boundary: this layer points at the established protein recovery owner.
------------------------------------------------------------------------

proteinRecoverySurface : Set₁
proteinRecoverySurface = Recovery.ProteinRecoveryBoundary

------------------------------------------------------------------------
-- WrongType / promotion firewalls.
------------------------------------------------------------------------

data GenomeCreatesExpressedProteinState : Set where
data SequenceCreatesConformation : Set where
data ConformationCreatesFunction : Set where
data CurrentVisibleStateCreatesHistory : Set where
data ObserverAgreementCreatesWorldCompleteness : Set where
data ExternalIdentityCreatesBiologicalAuthority : Set where
data CrossDomainWitnessTransfersMechanism : Set where

genomeDoesNotCreateExpressedProteinState : GenomeCreatesExpressedProteinState → ⊥
genomeDoesNotCreateExpressedProteinState ()

sequenceDoesNotCreateConformation : SequenceCreatesConformation → ⊥
sequenceDoesNotCreateConformation ()

conformationDoesNotCreateFunction : ConformationCreatesFunction → ⊥
conformationDoesNotCreateFunction ()

visibleStateDoesNotCreateHistory : CurrentVisibleStateCreatesHistory → ⊥
visibleStateDoesNotCreateHistory ()

observerAgreementDoesNotCreateWorldCompleteness : ObserverAgreementCreatesWorldCompleteness → ⊥
observerAgreementDoesNotCreateWorldCompleteness ()

externalIdentityDoesNotCreateBiologicalAuthority : ExternalIdentityCreatesBiologicalAuthority → ⊥
externalIdentityDoesNotCreateBiologicalAuthority ()

crossDomainWitnessDoesNotTransferMechanism : CrossDomainWitnessTransfersMechanism → ⊥
crossDomainWitnessDoesNotTransferMechanism ()

------------------------------------------------------------------------
-- Attribution rule.
------------------------------------------------------------------------

attributionRule : String
attributionRule =
  "DOI/PMID/PMCID/QID/PDB/UniProt identify sources or objects and retain provenance only. Empirical sources own only their acquired propositions; SituatedProteinQueryWitness and the generic factorisation/refinement structure are DASHI synthesis. Cross-domain reuse transfers structure, not authorship, mechanism, truth or biological authority."

------------------------------------------------------------------------
-- Boundary.
------------------------------------------------------------------------

record ProteinSituatedHyperfabricBoundary : Set where
  constructor protein-situated-hyperfabric-boundary
  field
    queryRelativeProjectionRequired : Bool
    missingCoordinateRetainedByRefinement : Bool
    observerIsPartOfSituatedState : Bool
    historyCoordinateRepresentable : Bool
    proteinRecoveryBoundaryReused : Bool
    proteinIdentityIsCompletePredictiveState : Bool
    genomeDeterminesExpressedProteinState : Bool
    sequenceDeterminesConformation : Bool
    conformationDeterminesFunction : Bool
    observerAgreementCreatesWorldCompleteness : Bool
    externalIdentityCreatesBiologicalAuthority : Bool
    crossDomainWitnessTransfersMechanism : Bool
open ProteinSituatedHyperfabricBoundary public

canonicalProteinSituatedHyperfabricBoundary : ProteinSituatedHyperfabricBoundary
canonicalProteinSituatedHyperfabricBoundary =
  protein-situated-hyperfabric-boundary
    true true true true true
    false false false false false false false
