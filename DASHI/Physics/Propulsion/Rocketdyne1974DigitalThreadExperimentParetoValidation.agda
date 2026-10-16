{-# OPTIONS --safe #-}
module DASHI.Physics.Propulsion.Rocketdyne1974DigitalThreadExperimentParetoValidation where

import DASHI.Physics.Propulsion.Rocketdyne1974DigitalThreadExperimentParetoExact as R
import DASHI.Physics.Propulsion.Rocketdyne1974ContemporaryQualificationPHMSourceAtlasExact as S

frontierExists : R.RocketdyneDigitalThreadExperimentFrontier
frontierExists = R.rocketdyneDigitalThreadExperimentFrontier

paretoBundleExists : R.AcquisitionPortfolio
paretoBundleExists = R.rocketdyneAcquisitionPortfolio

digitalThreadBoundaryExists : R.DigitalThreadBoundary
digitalThreadBoundaryExists = R.digitalThreadBoundary

sourceAtlasBoundaryExists : S.ContemporarySourceAtlasBoundary
sourceAtlasBoundaryExists = S.contemporarySourceAtlasBoundary
