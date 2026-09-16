module DASHI.Biology.Protein.ProteinConsumerProjectionAdequacyExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Equality using (_≡_)
open import Data.Empty using (⊥)

import DASHI.Core.QueryIndexedProjectionAdequacyExact as Query
import DASHI.Biology.Protein.ProteinSituatedHyperfabricExact as Situated
import DASHI.Biology.Protein.TRPA1SingleResidueThermalAdaptationExact as TRPA1Core
import DASHI.Biology.Protein.TRPA1SituatedProteinWitnessExact as TRPA1
import DASHI.Biology.Protein.TRPA1SourceAttributionEnvelopeExact as TRPA1Source
import DASHI.Biology.Protein.AdenylateKinaseSituatedProteinWitnessExact as AdK
import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseConformationalEmpiricalExact as AdKCore
import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseRateObserverAdequacyExact as Rate
import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseCalibrationAttributionEnvelopeExact as AdKSource

------------------------------------------------------------------------
-- PROTEIN CONSUMER-PROJECTION ADEQUACY PORTFOLIO
--
-- This owner composes three already-paid information-loss witnesses.  It does
-- not introduce a universal protein ontology and it does not claim that one
-- repaired observation is sufficient for every protein consumer.
--
--   TRPA1 thermal query : protein identity is too coarse; retain residue state.
--   AdK conformation    : sequence is too coarse; retain environment/context.
--   AdK transition rate : route topology is too coarse; retain rate coordinate.
--
-- The empirical/source propositions remain owned by their original sources.
-- The portfolio and the query-indexed comparison are DASHI synthesis.
------------------------------------------------------------------------

data ProteinConsumer : Set where
  thermalResponseConsumer : ProteinConsumer
  resolvedConformationConsumer : ProteinConsumer
  transitionRateConsumer : ProteinConsumer

data ProteinCoordinateClass : Set where
  proteinIdentityCoordinate : ProteinCoordinateClass
  sequenceResidueCoordinate : ProteinCoordinateClass
  conformationCoordinate : ProteinCoordinateClass
  environmentCoordinate : ProteinCoordinateClass
  perturbationCoordinate : ProteinCoordinateClass
  assayCoordinate : ProteinCoordinateClass
  observableDefinitionCoordinate : ProteinCoordinateClass
  routeTopologyCoordinate : ProteinCoordinateClass
  rateCoordinate : ProteinCoordinateClass
  sourceProvenanceCoordinate : ProteinCoordinateClass

record ConsumerProjectionProfile : Set where
  constructor consumer-projection-profile
  field
    consumer : ProteinConsumer
    coarseProjection : String
    separatingCoordinate : ProteinCoordinateClass
    enrichedObservation : String
    sourcePayment : String
    dashiRole : String
open ConsumerProjectionProfile public

thermalProjectionProfile : ConsumerProjectionProfile
thermalProjectionProfile = consumer-projection-profile
  thermalResponseConsumer
  "TRPA1 protein identity"
  sequenceResidueCoordinate
  "TRPA1 protein identity + pore-residue state"
  "Feng et al. 2026 source-bounded comparative/mutational thermal-gating result; DOI 10.1126/sciadv.aee3948, PMID 42685214, PMCID PMC13537265; article QID unresolved"
  "DASHI query-indexed projection defect and repair comparison"

conformationProjectionProfile : ConsumerProjectionProfile
conformationProjectionProfile = consumer-projection-profile
  resolvedConformationConsumer
  "adenylate-kinase primary sequence"
  environmentCoordinate
  "same sequence + ligand/environment context in the finite 4AKE/1AKE fixture"
  "4AKE/1AKE structural depositions and associated primary literature pay the bounded same-sequence/distinct-conformation observation; PDB/UniProt/QID remain provenance coordinates"
  "DASHI query-indexed situated-protein comparison"

rateProjectionProfile : ConsumerProjectionProfile
rateProjectionProfile = consumer-projection-profile
  transitionRateConsumer
  "AdK route topology"
  rateCoordinate
  "route topology + retained rate coordinate"
  "Li, Liu & Ji 2015 pays the source-bounded Kramers-rate coordinate/methodology and calibration roles; DOI 10.1016/j.bpj.2015.06.059, PMID 26244746, PMCID PMC4572606; article QID unresolved"
  "DASHI query-adequacy collision and enriched-observer repair"

------------------------------------------------------------------------
-- The three theorem-bearing defects are inherited, not recreated.
------------------------------------------------------------------------

thermalIdentityNotAdequate :
  Query.AdequateFor
    TRPA1Core.proteinIdentity
    TRPA1.thermalSemantics
    TRPA1.thermalResponseQuery →
  ⊥
thermalIdentityNotAdequate = TRPA1.proteinIdentityNotAdequateForThermalQuery

conformationSequenceNotAdequate :
  Query.AdequateFor
    AdKCore.primarySequence
    AdK.conformationSemantics
    AdK.resolvedConformationQuery →
  ⊥
conformationSequenceNotAdequate = AdK.sequenceNotAdequateForConformationQuery

transitionRateTopologyNotAdequate :
  Query.AdequateFor
    Rate.topologyProjection
    Rate.rateSemantics
    Rate.transitionRateQuery →
  ⊥
transitionRateTopologyNotAdequate = Rate.topologyTransitionRateNotAdequate

------------------------------------------------------------------------
-- Constructive local repairs remain consumer-specific.
------------------------------------------------------------------------

thermalResidueRepair :
  (x : TRPA1Core.TRPA1RichState) →
  TRPA1Core.thermalReadout x ≡
  TRPA1Core.thermalFromResidueAware (TRPA1Core.residueAware x)
thermalResidueRepair = TRPA1Core.thermalResponseFactorsThroughResidueAware

conformationEnvironmentRepair :
  (x : AdKCore.AdKResolvedState) →
  AdKCore.conformation x ≡
  AdKCore.stateFromEnvironment (AdKCore.environment x)
conformationEnvironmentRepair = AdKCore.environmentPaysFixture

transitionRateCoordinateRepair :
  Query.AdequateFor
    Rate.enrichedProjection
    Rate.rateSemantics
    Rate.transitionRateQuery
transitionRateCoordinateRepair = Rate.enrichedTransitionRateAdequate

------------------------------------------------------------------------
-- Attribution/source-role donors.
------------------------------------------------------------------------

situatedProteinBoundary = Situated.canonicalProteinSituatedHyperfabricBoundary
trpa1AttributionBoundary = TRPA1Source.canonicalTRPA1SourceAttributionBoundary
adkAttributionSource = AdKSource.liLiuJiSource

attributionRule : String
attributionRule =
  "Feng/TRPA1, the 4AKE/1AKE structural sources, and Li-Liu-Ji/AdK retain ownership only of their acquired domain propositions. DOI/PMID/PMCID/QID/PDB/UniProt identify publications or objects and retain provenance; they do not create a biological proposition. The shared consumer-projection portfolio, FactorsThrough defects, and cross-domain comparison are DASHI synthesis. A repair paid for one consumer or protein lane cannot be transferred to another without a separate witness."

------------------------------------------------------------------------
-- WrongType / cross-domain firewalls.
------------------------------------------------------------------------

data ThermalResidueRepairCreatesAdKRate : Set where
data EnvironmentRepairCreatesTRPA1ThermalLaw : Set where
data RateCoordinateCreatesConformation : Set where
data CrossDomainAttributionTransfers : Set where
data ExternalIdentityCreatesBiologicalAuthority : Set where
data OneRepairSufficesForEveryProteinConsumer : Set where

thermalRepairDoesNotCreateAdkRate : ThermalResidueRepairCreatesAdKRate → ⊥
thermalRepairDoesNotCreateAdkRate ()

environmentRepairDoesNotCreateTrpa1ThermalLaw : EnvironmentRepairCreatesTRPA1ThermalLaw → ⊥
environmentRepairDoesNotCreateTrpa1ThermalLaw ()

rateCoordinateDoesNotCreateConformation : RateCoordinateCreatesConformation → ⊥
rateCoordinateDoesNotCreateConformation ()

crossDomainAttributionDoesNotTransfer : CrossDomainAttributionTransfers → ⊥
crossDomainAttributionDoesNotTransfer ()

externalIdentityDoesNotCreateBiologicalAuthority : ExternalIdentityCreatesBiologicalAuthority → ⊥
externalIdentityDoesNotCreateBiologicalAuthority ()

oneRepairDoesNotSufficeForEveryConsumer : OneRepairSufficesForEveryProteinConsumer → ⊥
oneRepairDoesNotSufficeForEveryConsumer ()

------------------------------------------------------------------------
-- Canonical boundary.
------------------------------------------------------------------------

record ProteinConsumerProjectionBoundary : Set where
  constructor protein-consumer-projection-boundary
  field
    thermalIdentityProjectionInadequate : Bool
    sequenceProjectionInadequateForConformation : Bool
    topologyProjectionInadequateForRate : Bool
    residueAwareThermalRepairRetained : Bool
    environmentAwareConformationRepairRetained : Bool
    rateCoordinateRepairRetained : Bool
    queryRelativeProjectionArchitectureReused : Bool
    sourceRolesRemainDomainLocal : Bool
    crossDomainAttributionTransfer : Bool
    externalIdentityCreatesBiologicalAuthority : Bool
    oneRepairSufficesForEveryProteinConsumer : Bool
open ProteinConsumerProjectionBoundary public

canonicalProteinConsumerProjectionBoundary : ProteinConsumerProjectionBoundary
canonicalProteinConsumerProjectionBoundary = protein-consumer-projection-boundary
  true true true
  true true true
  true true
  false false false
