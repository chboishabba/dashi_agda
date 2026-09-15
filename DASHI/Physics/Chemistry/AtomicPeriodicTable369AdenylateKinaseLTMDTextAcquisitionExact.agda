module DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseLTMDTextAcquisitionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as Snowball
import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseSparseCalibrationFibreExact as Sparse
import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseCalibrationAttributionEnvelopeExact as Attr

------------------------------------------------------------------------
-- MACHINE-READABLE LT-MD TEXT ACQUISITION
--
-- This owner records only transition coordinates stated in article prose.
-- These are simulation observations / simulation-time statements, not Kramers
-- rate constants and not experimental kinetic measurements.
------------------------------------------------------------------------

source : Attribution.AttributedSource
source = Sparse.liLiuJi2015Source

sourceReceipt : Snowball.SourceRoleSnowballReceipt source
sourceReceipt = Snowball.canonicalSourceRoleSnowballReceipt source

articleEnvelope : Attr.CalibrationAttributionEnvelope
articleEnvelope = Attr.canonicalLiLiuJiCalibrationAttributionEnvelope

data LTMDObservationKind : Set where
  simulationAngleObservation : LTMDObservationKind
  simulationTimescaleObservation : LTMDObservationKind
  simulationNonReachabilityObservation : LTMDObservationKind
  simulationTrajectoryRange : LTMDObservationKind

record LTMDTextObservation : Set where
  constructor ltmd-text-observation
  field
    label : String
    kind : LTMDObservationKind
    value : String
    sourceLocator : String
    sourceIdentity : Attribution.AttributedSource
    interpretation : String
open LTMDTextObservation public

ligandBoundThetaTwoIntermediate : LTMDTextObservation
ligandBoundThetaTwoIntermediate = ltmd-text-observation
  "ATP+AMP open-start NMP intermediate"
  simulationAngleObservation
  "theta2 approximately 45 degrees"
  "PMC4572606 Results: ligands binding impacts; Figs. 3a/S7"
  source
  "simulation-observed NMP intermediate coordinate; not a named Figure-5 state identity and not an experimental population"

ligandBoundLidClosureTimescale : LTMDTextObservation
ligandBoundLidClosureTimescale = ltmd-text-observation
  "ATP+AMP open-start LID closure timescale"
  simulationTimescaleObservation
  "approximately 50-100 ns"
  "PMC4572606 Results: ligands binding impacts; Figs. 3a/S7"
  source
  "simulation trajectory timescale for this setup; not a universal rate constant"

ligandBoundNoFullClosureAtOneMicrosecond : LTMDTextObservation
ligandBoundNoFullClosureAtOneMicrosecond = ltmd-text-observation
  "ATP+AMP open-start full-closure non-observation"
  simulationNonReachabilityObservation
  "no transition to fully closed PDB-1AKE-like conformation by 1000 ns"
  "PMC4572606 Results: ligands binding impacts; Figs. 3a/S7"
  source
  "finite simulation non-observation only; not a proof that full closure is impossible"

closedBoundStartingAngles : LTMDTextObservation
closedBoundStartingAngles = ltmd-text-observation
  "closed-start ATP+Mg2+-AMP stabilized angles"
  simulationAngleObservation
  "theta1 approximately 65 degrees; theta2 approximately 30 degrees"
  "PMC4572606 Results: ligand-bound closed-start trajectory; Figs. 3d/S10"
  source
  "simulation coordinate observation near closed conformation; not replacement for the crystal endpoint coordinates"

closedBoundNmpExcursion : LTMDTextObservation
closedBoundNmpExcursion = ltmd-text-observation
  "closed-start NMP angular excursion"
  simulationTrajectoryRange
  "after approximately 125 ns, theta2 increased from approximately 30 to approximately 45 degrees within a few ns"
  "PMC4572606 Results: ligand-bound closed-start trajectory; Figs. 3d/S10"
  source
  "simulation trajectory event; not an experimental transition-rate measurement"

ligandFreeOpenStartAngularRange : LTMDTextObservation
ligandFreeOpenStartAngularRange = ltmd-text-observation
  "ligand-free open-start LT-MD angular range"
  simulationTrajectoryRange
  "theta1 approximately 95 to 60 degrees; theta2 approximately 65 to 35 degrees"
  "PMC4572606 Mapping transitions/pathways from LT-MD; Figure 4a"
  source
  "source-text trajectory range: LID reaches closed-like angle while NMP reaches semi-open range; does not identify a unique pathway state"

------------------------------------------------------------------------
-- Attribution / WrongType firewalls.
------------------------------------------------------------------------

data SimulationObservationIsExperimentalKinetics : Set where
data FiniteNonObservationProvesImpossibility : Set where
data ApproximateTimescaleCreatesKramersRate : Set where
data ArticleIdentityCreatesTrajectoryValue : Set where

aSimulationObservationDoesNotBecomeExperimentalKinetics :
  SimulationObservationIsExperimentalKinetics → ⊥
aSimulationObservationDoesNotBecomeExperimentalKinetics ()

finiteNonObservationDoesNotProveImpossibility :
  FiniteNonObservationProvesImpossibility → ⊥
finiteNonObservationDoesNotProveImpossibility ()

approximateTimescaleDoesNotCreateKramersRate :
  ApproximateTimescaleCreatesKramersRate → ⊥
approximateTimescaleDoesNotCreateKramersRate ()

articleIdentityDoesNotCreateTrajectoryValue :
  ArticleIdentityCreatesTrajectoryValue → ⊥
articleIdentityDoesNotCreateTrajectoryValue ()

------------------------------------------------------------------------
-- Boundary.
------------------------------------------------------------------------

record AdKLTMDTextAcquisitionBoundary : Set where
  constructor adk-ltmd-text-acquisition-boundary
  field
    ligandBoundThetaTwoIntermediatePaid : Bool
    ligandBoundClosureTimescalePaid : Bool
    finiteOneMicrosecondNonClosurePaid : Bool
    closedBoundStartingAnglesPaid : Bool
    closedBoundNmpExcursionPaid : Bool
    ligandFreeAngularRangePaid : Bool
    fullClosureObservedWithinOneMicrosecond : Bool
    simulationObservationEqualsExperimentalKinetics : Bool
    approximateTimescaleEqualsKramersRate : Bool
    articleAttributionEnvelopeRetained : Bool
    unresolvedArticleQidBlocksObservation : Bool
    nextResidual : String
open AdKLTMDTextAcquisitionBoundary public

canonicalAdKLTMDTextAcquisitionBoundary : AdKLTMDTextAcquisitionBoundary
canonicalAdKLTMDTextAcquisitionBoundary = adk-ltmd-text-acquisition-boundary
  true true true true true true
  false false false true false
  "retain these LT-MD prose observations as simulation-observed coordinates. Do not substitute them for Figure-5 Kramers edge rates or experiment; continue acquiring same-object supplement/figure cells for intermediate dLN, per-state Delta-G, and per-edge Kramers numerics."
