module DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseLigandBoundGeometryTextAcquisitionValidation where

open import DASHI.Core.Prelude

import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseLigandBoundGeometryTextAcquisitionExact as Target

-- RED-first validation surface for machine-readable ligand-bound geometry facts.

closedClusterThetaOnePaid : Bool
closedClusterThetaOnePaid = Target.closedClusterThetaOnePaid

closedClusterThetaTwoPaid : Bool
closedClusterThetaTwoPaid = Target.closedClusterThetaTwoPaid

unfavourableRegionPaid : Bool
unfavourableRegionPaid = Target.unfavourableRegionPaid

favouredPathPaid : Bool
favouredPathPaid = Target.favouredPathPaid

gammaLExactCoordinatePaid : Bool
gammaLExactCoordinatePaid = Target.gammaLExactCoordinatePaid

intermediateDLnNamedStatePaid : Bool
intermediateDLnNamedStatePaid = Target.intermediateDLnNamedStatePaid

boundary = Target.canonicalLigandBoundGeometryTextBoundary
