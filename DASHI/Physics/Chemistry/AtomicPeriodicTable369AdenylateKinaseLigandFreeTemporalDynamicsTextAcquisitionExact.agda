module DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseLigandFreeTemporalDynamicsTextAcquisitionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as Snowball
import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseCalibrationAttributionEnvelopeExact as Attr

------------------------------------------------------------------------
-- LIGAND-FREE LT-MD TEMPORAL DYNAMICS TEXT ACQUISITION
--
-- Li-Liu-Ji machine-readable prose pays a small set of temporal observations
-- that are useful independently of Figure-5 Kramers numerics:
--   * in typical ligand-free open-start LT-MD, LID can close on ~10 ns and
--     reopen on ~100 ns timescales;
--   * open <-> semi-open/semi-closed switching is reported on ~100--800 ns;
--   * three cracking regions are identified at residues 60--63, 110--120 and
--     160--175, with secondary-structure switching on ~10--100 ns timescales.
--
-- These are simulation-observed temporal/structural statements. They are not
-- Kramers edge-rate constants, experimental kinetics, universal dwell times,
-- or proof that every trajectory follows the same timing.
------------------------------------------------------------------------

source : Attribution.AttributedSource
source = Attr.liLiuJiSource

sourceReceipt : Snowball.SourceRoleSnowballReceipt source
sourceReceipt = Snowball.canonicalSourceRoleSnowballReceipt source

articleDOI = Attr.articleDOI
articlePMID = Attr.articlePMID
articlePMCID = Attr.articlePMCID
articleQID = Attr.articleQID
adkQID = Attr.adkQID
adkUniProt = Attr.adkUniProt

data TemporalObservationKind : Set where
  approximateEventTimescale : TemporalObservationKind
  approximateCycleWindow : TemporalObservationKind
  residueRegionObservation : TemporalObservationKind
  structuralSwitchTimescale : TemporalObservationKind

record TemporalDynamicsObservation : Set where
  constructor temporal-dynamics-observation
  field
    label : String
    kind : TemporalObservationKind
    value : String
    sourceLocator : String
    interpretation : String
open TemporalDynamicsObservation public

ligandFreeLidClosure : TemporalDynamicsObservation
ligandFreeLidClosure = temporal-dynamics-observation
  "ligand-free open-start LID closure"
  approximateEventTimescale
  "approximately 10 ns"
  "Li-Liu-Ji 2015 Results, ligand-free LT-MD; Figs. 2a/S1"
  "typical simulation event timescale for LID closing; not a rate constant or universal dwell time"

ligandFreeLidReopen : TemporalDynamicsObservation
ligandFreeLidReopen = temporal-dynamics-observation
  "ligand-free open-start LID reopening"
  approximateEventTimescale
  "approximately 100 ns"
  "Li-Liu-Ji 2015 Results, ligand-free LT-MD; Figs. 2a/S1"
  "typical simulation event timescale for LID reopening after closure; not an experimental relaxation time"

openSemiOpenCycleWindow : TemporalDynamicsObservation
openSemiOpenCycleWindow = temporal-dynamics-observation
  "ligand-free open/semi-open-semi-closed switching window"
  approximateCycleWindow
  "approximately 100-800 ns"
  "Li-Liu-Ji 2015 Discussion: reversible large-scale conformational transitions in ~100-800 ns LT-MD window"
  "reported LT-MD switching window; does not imply a single exponential process or one edge rate"

crackingRegionOne : TemporalDynamicsObservation
crackingRegionOne = temporal-dynamics-observation
  "cracking region 1"
  residueRegionObservation
  "residues 60-63"
  "Li-Liu-Ji 2015 Discussion: Rate-limiting step and domain-transition order"
  "source-identified cracking region correlated with large conformational transitions"

crackingRegionTwo : TemporalDynamicsObservation
crackingRegionTwo = temporal-dynamics-observation
  "cracking region 2"
  residueRegionObservation
  "residues 110-120"
  "Li-Liu-Ji 2015 Discussion: Rate-limiting step and domain-transition order"
  "source-identified cracking region overlapping helix alpha6; role remains source-bounded"

crackingRegionThree : TemporalDynamicsObservation
crackingRegionThree = temporal-dynamics-observation
  "cracking region 3"
  residueRegionObservation
  "residues 160-175"
  "Li-Liu-Ji 2015 Discussion: Rate-limiting step and domain-transition order"
  "source-identified cracking region overlapping helix alpha7; role remains source-bounded"

crackingSwitchTimescale : TemporalDynamicsObservation
crackingSwitchTimescale = temporal-dynamics-observation
  "secondary-structure switching in cracking regions"
  structuralSwitchTimescale
  "approximately 10-100 ns"
  "Li-Liu-Ji 2015 Discussion; Figure S17 reference"
  "simulation-observed switching timescale for the identified regions; not a universal unfolding/refolding rate"

ligandFreeTemporalObservations : List TemporalDynamicsObservation
ligandFreeTemporalObservations =
  ligandFreeLidClosure ∷ ligandFreeLidReopen ∷ openSemiOpenCycleWindow ∷
  crackingRegionOne ∷ crackingRegionTwo ∷ crackingRegionThree ∷
  crackingSwitchTimescale ∷ []

------------------------------------------------------------------------
-- WrongType / attribution firewalls.
------------------------------------------------------------------------

data SimulationTimescaleEqualsKramersRate : Set where
data SimulationTimescaleEqualsExperimentalKinetics : Set where
data ApproximateWindowCreatesSingleRateConstant : Set where
data CrackingRegionCreatesUniversalMechanism : Set where
data QidCreatesTemporalAuthority : Set where

data SourceCorrelationCreatesCausalNecessity : Set where

simulationTimescaleDoesNotEqualKramersRate : SimulationTimescaleEqualsKramersRate → ⊥
simulationTimescaleDoesNotEqualKramersRate ()

simulationTimescaleDoesNotEqualExperiment : SimulationTimescaleEqualsExperimentalKinetics → ⊥
simulationTimescaleDoesNotEqualExperiment ()

windowDoesNotCreateSingleRate : ApproximateWindowCreatesSingleRateConstant → ⊥
windowDoesNotCreateSingleRate ()

crackingRegionDoesNotCreateUniversalMechanism : CrackingRegionCreatesUniversalMechanism → ⊥
crackingRegionDoesNotCreateUniversalMechanism ()

qidDoesNotCreateTemporalAuthority : QidCreatesTemporalAuthority → ⊥
qidDoesNotCreateTemporalAuthority ()

correlationDoesNotCreateCausalNecessity : SourceCorrelationCreatesCausalNecessity → ⊥
correlationDoesNotCreateCausalNecessity ()

------------------------------------------------------------------------
-- Boundary.
------------------------------------------------------------------------

record LigandFreeTemporalDynamicsTextBoundary : Set where
  constructor ligand-free-temporal-dynamics-text-boundary
  field
    lidClosureTenNsPaid : Bool
    lidReopenHundredNsPaid : Bool
    openSemiOpenCycleHundredToEightHundredNsPaid : Bool
    threeCrackingRegionsPaid : Bool
    crackingTenToHundredNsPaid : Bool
    simulationTimescaleEqualsKramersRate : Bool
    simulationTimescaleEqualsExperimentalKinetics : Bool
    approximateWindowCreatesSingleRate : Bool
    crackingCreatesUniversalMechanism : Bool
    sourceCorrelationCreatesCausalNecessity : Bool
    qidCreatesTemporalAuthority : Bool
    doiPmidPmcidRetained : Bool
    articleQidMayRemainUnresolved : Bool
open LigandFreeTemporalDynamicsTextBoundary public

canonicalLigandFreeTemporalDynamicsTextBoundary : LigandFreeTemporalDynamicsTextBoundary
canonicalLigandFreeTemporalDynamicsTextBoundary =
  ligand-free-temporal-dynamics-text-boundary
    true true true true true
    false false false false false false
    true true
