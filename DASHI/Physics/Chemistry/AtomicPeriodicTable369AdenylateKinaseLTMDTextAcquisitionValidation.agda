module DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseLTMDTextAcquisitionValidation where

open import DASHI.Core.Prelude
import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseLTMDTextAcquisitionExact as LTMD

-- RED-first validation surface for machine-readable LT-MD text acquisition.
-- It deliberately validates source-role separation rather than compiler/CI state.

boundary : LTMD.AdKLTMDTextAcquisitionBoundary
boundary = LTMD.canonicalAdKLTMDTextAcquisitionBoundary

ligandBoundIntermediatePaid : Bool
ligandBoundIntermediatePaid = LTMD.ligandBoundThetaTwoIntermediatePaid boundary

ligandBoundTimescalePaid : Bool
ligandBoundTimescalePaid = LTMD.ligandBoundClosureTimescalePaid boundary

fullClosureObserved : Bool
fullClosureObserved = LTMD.fullClosureObservedWithinOneMicrosecond boundary

simulationObservationIsExperimentalRate : Bool
simulationObservationIsExperimentalRate = LTMD.simulationObservationEqualsExperimentalKinetics boundary

articleIdentityRetained : Bool
articleIdentityRetained = LTMD.articleAttributionEnvelopeRetained boundary
