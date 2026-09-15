module DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseIntermediateGeometryTextAcquisitionValidation where

open import DASHI.Core.Prelude

import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseIntermediateGeometryTextAcquisitionExact as Target

------------------------------------------------------------------------
-- RED-first validation surface for source-text acquisition of the ligand-free
-- semi-open/semi-closed geometry envelope.  This must remain a region-level
-- simulation observation, not a named-state dLN table or experimental state.
------------------------------------------------------------------------

intermediateEnvelope = Target.ligandFreeIntermediateGeometryEnvelope
nmpSemiOpenEnvelope = Target.nmpSemiOpenThetaTwoEnvelope

boundary = Target.canonicalAdKIntermediateGeometryTextAcquisitionBoundary

intermediateThetaOnePaid : Bool
intermediateThetaOnePaid = Target.AdKIntermediateGeometryTextAcquisitionBoundary.intermediateThetaOneRangePaid boundary

intermediateThetaTwoPaid : Bool
intermediateThetaTwoPaid = Target.AdKIntermediateGeometryTextAcquisitionBoundary.intermediateThetaTwoRangePaid boundary

intermediateDLnPaid : Bool
intermediateDLnPaid = Target.AdKIntermediateGeometryTextAcquisitionBoundary.intermediateDLnRangePaid boundary

namedStateDLnStillUnpaid : Bool
namedStateDLnStillUnpaid = Target.AdKIntermediateGeometryTextAcquisitionBoundary.namedStateDLnTablePaid boundary

regionDoesNotBecomeNamedState : Bool
regionDoesNotBecomeNamedState = Target.AdKIntermediateGeometryTextAcquisitionBoundary.regionEnvelopeEqualsNamedFigureState boundary

simulationDoesNotBecomeExperiment : Bool
simulationDoesNotBecomeExperiment = Target.AdKIntermediateGeometryTextAcquisitionBoundary.simulationEnvelopeEqualsExperimentalState boundary
