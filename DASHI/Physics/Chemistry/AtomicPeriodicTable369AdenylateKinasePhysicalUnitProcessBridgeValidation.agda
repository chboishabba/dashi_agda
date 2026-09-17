module DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinasePhysicalUnitProcessBridgeValidation where

-- Focused regression root for the bounded physical-unit/process continuation.
-- Every imported validation owner was committed before its production owner.
import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseSIQuantityBridgeValidation
import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseChemicalSystemValidation
import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinasePhysicalDynamicsBridgeValidation

-- Geometry-all-the-way-down continuation: indexed atomistic configuration,
-- source-owned typed selections, mass-weighted COM/SE(3) geometry and the
-- inhabited Configuration -> (theta1, theta2, dLN) projection.
import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseAtomisticConfigurationValidation
import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseSourceAtomSelectionValidation
import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseCOMGeometryValidation
import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseAtomisticCVProjectionValidation

-- Same-object fixture/mechanics/executable-comparison/trajectory continuation.
-- PDB entry identity is kept apart from chain/coordinate manifestation;
-- historical mechanics settings are source-paid without claiming exact bytes;
-- OpenMM remains a non-authoritative, unexecuted oracle contract; trajectory
-- lifting retains lower frames through CV observations and state classification.
import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinasePDBAtomisticFixtureValidation
import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseHistoricalMechanicsValidation
import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseOpenMMCVOracleValidation
import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseAtomisticTrajectoryLiftValidation
