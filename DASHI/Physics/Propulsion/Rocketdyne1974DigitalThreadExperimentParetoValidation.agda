{-# OPTIONS --safe #-}
module DASHI.Physics.Propulsion.Rocketdyne1974DigitalThreadExperimentParetoValidation where

import DASHI.Physics.Propulsion.Rocketdyne1974DigitalThreadExperimentParetoExact as R

frontierExists : R.RocketdyneDigitalThreadExperimentFrontier
frontierExists = R.rocketdyneDigitalThreadExperimentFrontier

paretoBundleExists : R.AcquisitionPortfolio
paretoBundleExists = R.rocketdyneAcquisitionPortfolio

digitalThreadBoundaryExists : R.DigitalThreadBoundary
digitalThreadBoundaryExists = R.digitalThreadBoundary
