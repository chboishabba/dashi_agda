module DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseLTMDProtocolAcquisitionValidation where

import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseLTMDProtocolAcquisitionExact as Protocol

open Protocol

-- RED-first validation surface for the machine-readable LT-MD protocol.
-- The source pays method/setup coordinates only; it does not turn those setup
-- parameters into state values, rates, experimental kinetics, or universal
-- force-field truth.

boundary = canonicalAdKLTMDProtocolAcquisitionBoundary

forceFieldPaid =
  AdKLTMDProtocolAcquisitionBoundary.ffamber03Paid boundary

ligandParameterLineagePaid =
  AdKLTMDProtocolAcquisitionBoundary.atpAmpParameterLineagePaid boundary

solvationSetupPaid =
  AdKLTMDProtocolAcquisitionBoundary.tip3pSolvationSetupPaid boundary

minimizationHeatingPaid =
  AdKLTMDProtocolAcquisitionBoundary.minimizationHeatingProtocolPaid boundary

productionDynamicsPaid =
  AdKLTMDProtocolAcquisitionBoundary.productionDynamicsProtocolPaid boundary

methodSourceDoisRetained =
  AdKLTMDProtocolAcquisitionBoundary.methodSourceDoisRetained boundary

methodSourceQidsMayRemainUnresolved =
  AdKLTMDProtocolAcquisitionBoundary.methodSourceQidsMayRemainUnresolved boundary

protocolCreatesStateCalibration =
  AdKLTMDProtocolAcquisitionBoundary.protocolCreatesStateCalibration boundary

forceFieldCreatesUniversalMechanism =
  AdKLTMDProtocolAcquisitionBoundary.forceFieldCreatesUniversalMechanism boundary

methodCitationImportsAdKResult =
  AdKLTMDProtocolAcquisitionBoundary.methodCitationImportsAdKResult boundary
