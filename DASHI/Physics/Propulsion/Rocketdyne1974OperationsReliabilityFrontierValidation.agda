{-# OPTIONS --safe #-}
module DASHI.Physics.Propulsion.Rocketdyne1974OperationsReliabilityFrontierValidation where

import DASHI.Physics.Propulsion.Rocketdyne1974OperationsReliabilityFrontierExact as R

operationsFrontierExists : R.RocketdyneOperationsReliabilityFrontier
operationsFrontierExists = R.rocketdyneOperationsReliabilityFrontier

serviceabilityOpen : R.ServiceabilityPopulationBoundary
serviceabilityOpen = R.serviceabilityPopulationBoundary

maintenanceObligationExists : R.OperationsObligationBundle
maintenanceObligationExists = R.operationsObligations

reliabilityObligationExists : R.ReliabilityObligationBundle
reliabilityObligationExists = R.reliabilityObligations
