{-# OPTIONS --safe #-}
module DASHI.Physics.Propulsion.Rocketdyne1974TerminalPhysicalFrontierExact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Propulsion.Rocketdyne1974MaterialIdentityAndConstitutiveDataExact as Mat
import DASHI.Physics.Propulsion.Rocketdyne1974TwoMaterialDiscriminatorExact as Disc
import DASHI.Physics.Propulsion.Rocketdyne1974IdentifiabilityCutExact as Id
import DASHI.Physics.Propulsion.Rocketdyne1974ThermalModelValidationExact as Therm
import DASHI.Physics.Propulsion.Rocketdyne1974MaterialDependentThermalFalsifierExact as Fals
import DASHI.Physics.Propulsion.Rocketdyne1974LatestSourceComparisonNote as Latest
import DASHI.Physics.Propulsion.Rocketdyne1974ExperimentalCoordinateRefinementExact as CoordRef
import DASHI.Physics.Propulsion.Rocketdyne1974QualificationFeedbackWeldExact as QualFeed

------------------------------------------------------------------------
-- TERMINAL PUBLIC-SOURCE FRONTIER
--
-- The acquired public report pays material/coating identity, a source-tested
-- thermal model, a near-matched material/outcome discriminator, and exact
-- falsifiers for material-blind temperature-only model families.  The generic
-- experimental-coordinate machinery now also certifies that material identity
-- separates a collision left unresolved by equilibrium temperature alone.
--
-- The historical Haynes -> WC103 sequence inhabits a qualification-feedback
-- candidate shape, but formal review/approval and population-level post-change
-- reliability remain separate acquisitions.
------------------------------------------------------------------------

archiveGeometryExhaustedForUniqueStress : Bool
archiveGeometryExhaustedForUniqueStress = true

sameModelCalibrationStillOpen : Bool
sameModelCalibrationStillOpen = true

empiricalMaterialDependencePaid : Bool
empiricalMaterialDependencePaid = true

record TerminalPhysicalFrontier : Set where
  constructor terminal-physical-frontier
  field
    historicalMaterialIdentityPaid : Bool
    historicalCoatingIdentityPaid : Bool
    sourceValidatedThermalModelExistencePaid : Bool
    sameTemperatureOppositeOutcomePaid : Bool
    materialBlindTemperatureModelRefuted : Bool
    localWallThicknessPaid : Bool
    localRadiusStressGeometryPaid : Bool
    completeTest052NumericalFieldPaid : Bool
    sameArticleHaynesLawPaid : Bool
    sameArticleWC103VH101LawPaid : Bool
    calibratedStressCreepPredictionPaid : Bool
    currentExternalProducer : String
    stoppingRule : String

currentTerminalFrontier : TerminalPhysicalFrontier
currentTerminalFrontier =
  terminal-physical-frontier
    true true true true true
    false false false false false false
    "Recover exact nozzle wall-gauge/local contour and same-article temperature-dependent strength/creep/coating/boundary-condition data, or obtain an equivalent engineering drawing/test-analysis package."
    "Until those coordinates are paid, retain the archive-level empirical discriminator plus constructive non-identifiability theorem; do not manufacture a unique stress or creep lifetime."

materialReceipt : Mat.MaterialDataBoundary
materialReceipt = Mat.canonicalMaterialDataBoundary

discriminatorReceipt : Disc.TwoMaterialDiscriminator
discriminatorReceipt = Disc.currentDiscriminator

identifiabilityReceipt : Id.IdentifiabilityBoundary
identifiabilityReceipt = Id.canonicalIdentifiabilityBoundary

thermalReceipt : Therm.ThermalModelBoundary
thermalReceipt = Therm.canonicalThermalModelBoundary

materialDependenceReceipt : Fals.MaterialDependenceBoundary
materialDependenceReceipt = Fals.canonicalMaterialDependenceBoundary

contemporaryComparatorReceipt : Latest.ContemporaryComparatorBoundary
contemporaryComparatorReceipt = Latest.canonicalContemporaryComparatorBoundary

experimentalCoordinateReceipt : CoordRef.CoordinateAcquisitionFrontier
experimentalCoordinateReceipt = CoordRef.nextCoordinateAcquisitionFrontier

qualificationFeedbackReceipt : QualFeed.HistoricalFeedbackReceipt
qualificationFeedbackReceipt = QualFeed.rocketdyneHistoricalFeedbackReceipt

qualificationGovernanceBoundaryReceipt : QualFeed.Feedback.ReliabilityAdaptiveFeedbackBoundary
qualificationGovernanceBoundaryReceipt = QualFeed.adaptiveQualificationBoundaryReceipt
