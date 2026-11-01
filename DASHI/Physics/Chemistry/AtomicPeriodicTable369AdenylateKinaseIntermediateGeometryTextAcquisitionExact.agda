module DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseIntermediateGeometryTextAcquisitionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as Snowball
import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseSparseCalibrationFibreExact as Sparse
import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseCalibrationAttributionEnvelopeExact as Attr
import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseLTMDTextAcquisitionExact as LTMD

------------------------------------------------------------------------
-- SOURCE-TEXT INTERMEDIATE GEOMETRY ACQUISITION
--
-- Li, Liu & Ji explicitly describe ligand-free LT-MD intermediate structures
-- with a three-coordinate region:
--   theta1 ~= 60--70 degrees
--   theta2 ~= 35--60 degrees
--   dLN    ~= 16--30 Angstrom
-- and identify example snapshots at 300 ns (Fig. 2a), 160 ns (Fig. 2b), and
-- 200 ns (Fig. 2c).  They separately describe the NMP semi-open region as
-- theta2 ~= 35--45 degrees on an approximately 100 ns simulation timescale.
--
-- These are region-level simulation observations.  They do not pay a mapping
-- from any named BE-META state (alpha, beta, gamma, ...) to a unique dLN value,
-- and they are not experimental structural populations or Kramers rates.
------------------------------------------------------------------------

source : Attribution.AttributedSource
source = Sparse.liLiuJi2015Source

sourceReceipt : Snowball.SourceRoleSnowballReceipt source
sourceReceipt = Snowball.canonicalSourceRoleSnowballReceipt source

articleEnvelope : Attr.CalibrationAttributionEnvelope
articleEnvelope = Attr.canonicalLiLiuJiCalibrationAttributionEnvelope

ltmdBoundary : LTMD.AdKLTMDTextAcquisitionBoundary
ltmdBoundary = LTMD.canonicalAdKLTMDTextAcquisitionBoundary

record SourcePaidRange : Set where
  constructor source-paid-range
  field
    lower : Nat
    upper : Nat
    unit : String
    approximationRole : String
    sourceLocator : String
    sourceIdentity : Attribution.AttributedSource
open SourcePaidRange public

record IntermediateGeometryEnvelope : Set where
  constructor intermediate-geometry-envelope
  field
    thetaOne : SourcePaidRange
    thetaTwo : SourcePaidRange
    dLn : SourcePaidRange
    biologicalRole : String
    observationRole : String
open IntermediateGeometryEnvelope public

ligandFreeIntermediateGeometryEnvelope : IntermediateGeometryEnvelope
ligandFreeIntermediateGeometryEnvelope = intermediate-geometry-envelope
  (source-paid-range 60 70 "degrees"
    "approximately 60--70 degrees"
    "PMC4572606 Results: ligand-free LT-MD intermediate states; Fig. 2a-c and Figs. S1-S3"
    source)
  (source-paid-range 35 60 "degrees"
    "approximately 35--60 degrees"
    "PMC4572606 Results: ligand-free LT-MD intermediate states; Fig. 2a-c and Figs. S1-S3"
    source)
  (source-paid-range 16 30 "Angstrom"
    "approximately 16--30 Angstrom"
    "PMC4572606 Results: ligand-free LT-MD intermediate states; Fig. 2a-c and Figs. S1-S3"
    source)
  "semi-open--semi-closed structures in which LID is close to CORE and contacts NMP while NMP remains open and/or semi-open"
  "LT-MD simulation region; not a unique named BE-META state and not an experimental population"

nmpSemiOpenThetaTwoEnvelope : SourcePaidRange
nmpSemiOpenThetaTwoEnvelope = source-paid-range
  35 45 "degrees"
  "NMP semi-open theta2 range"
  "PMC4572606 Results: ligand-free LT-MD text; around 100 ns, including Fig. 2b/S2"
  source

record SnapshotReceipt : Set where
  constructor snapshot-receipt
  field
    timeNs : Nat
    locator : String
    role : String
open SnapshotReceipt public

figure2aIntermediateSnapshot : SnapshotReceipt
figure2aIntermediateSnapshot = snapshot-receipt 300
  "Figure 2a / LT-MD O1 snapshot at 300 ns"
  "example intermediate structure inside the source-paid region; not a region centroid"

figure2bIntermediateSnapshot : SnapshotReceipt
figure2bIntermediateSnapshot = snapshot-receipt 160
  "Figure 2b / LT-MD O2 snapshot at 160 ns"
  "example intermediate structure; source also uses this trajectory for NMP semi-open timing"

figure2cIntermediateSnapshot : SnapshotReceipt
figure2cIntermediateSnapshot = snapshot-receipt 200
  "Figure 2c / LT-MD O3 snapshot at 200 ns"
  "example intermediate structure inside the source-paid region"

record TimescaleEnvelope : Set where
  constructor timescale-envelope
  field
    approximateNs : Nat
    sourceLocator : String
    interpretation : String
open TimescaleEnvelope public

nmpSemiOpenTimescale : TimescaleEnvelope
nmpSemiOpenTimescale = timescale-envelope 100
  "PMC4572606 Results: ligand-free LT-MD; NMP can adopt semi-open state at ~100 ns"
  "simulation timescale observation for the studied setup; not a rate constant"

------------------------------------------------------------------------
-- WrongType / attribution firewalls.
------------------------------------------------------------------------

data RegionEnvelopeIsNamedFigureState : Set where
data RegionRangeCreatesUniqueDLn : Set where
data SimulationEnvelopeIsExperimentalState : Set where
data SnapshotTimeIsTransitionRate : Set where
data IdentityEnvelopeCreatesGeometry : Set where

regionEnvelopeDoesNotBecomeNamedFigureState : RegionEnvelopeIsNamedFigureState → ⊥
regionEnvelopeDoesNotBecomeNamedFigureState ()

regionRangeDoesNotCreateUniqueDLn : RegionRangeCreatesUniqueDLn → ⊥
regionRangeDoesNotCreateUniqueDLn ()

simulationEnvelopeDoesNotBecomeExperimentalState : SimulationEnvelopeIsExperimentalState → ⊥
simulationEnvelopeDoesNotBecomeExperimentalState ()

snapshotTimeDoesNotBecomeTransitionRate : SnapshotTimeIsTransitionRate → ⊥
snapshotTimeDoesNotBecomeTransitionRate ()

identityEnvelopeDoesNotCreateGeometry : IdentityEnvelopeCreatesGeometry → ⊥
identityEnvelopeDoesNotCreateGeometry ()

------------------------------------------------------------------------
-- Boundary.
------------------------------------------------------------------------

record AdKIntermediateGeometryTextAcquisitionBoundary : Set where
  constructor adk-intermediate-geometry-text-acquisition-boundary
  field
    intermediateThetaOneRangePaid : Bool
    intermediateThetaTwoRangePaid : Bool
    intermediateDLnRangePaid : Bool
    nmpSemiOpenThetaTwoRangePaid : Bool
    nmpSemiOpenTimescalePaid : Bool
    exampleSnapshotLocatorsPaid : Bool
    namedStateDLnTablePaid : Bool
    regionEnvelopeEqualsNamedFigureState : Bool
    simulationEnvelopeEqualsExperimentalState : Bool
    snapshotTimeEqualsTransitionRate : Bool
    attributionEnvelopeRetained : Bool
    articleQidRequiredForGeometryPayment : Bool
    nextResidual : String
open AdKIntermediateGeometryTextAcquisitionBoundary public

canonicalAdKIntermediateGeometryTextAcquisitionBoundary :
  AdKIntermediateGeometryTextAcquisitionBoundary
canonicalAdKIntermediateGeometryTextAcquisitionBoundary =
  adk-intermediate-geometry-text-acquisition-boundary
    true true true true true true
    false false false false
    true false
    "the source-text dLN unknown is narrowed from wholly absent to a ligand-free intermediate-region envelope of approximately 16--30 Angstrom. Do not assign that range or any midpoint to beta/gamma/delta/epsilon individually. Remaining same-object numerical debts are named-state dLN, per-state Figure-5 relative free energies, and per-edge Kramers rates."
