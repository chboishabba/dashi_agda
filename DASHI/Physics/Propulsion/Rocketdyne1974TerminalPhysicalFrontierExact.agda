{-# OPTIONS --safe #-}
module DASHI.Physics.Propulsion.Rocketdyne1974TerminalPhysicalFrontierExact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Propulsion.Rocketdyne1974MaterialIdentityAndConstitutiveDataExact as Mat
import DASHI.Physics.Propulsion.Rocketdyne1974TwoMaterialDiscriminatorExact as Disc
import DASHI.Physics.Propulsion.Rocketdyne1974IdentifiabilityCutExact as Id
import DASHI.Physics.Propulsion.Rocketdyne1974ThermalModelValidationExact as Therm
import DASHI.Physics.Propulsion.Rocketdyne1974MaterialDependentThermalFalsifierExact as Fals

------------------------------------------------------------------------
-- TERMINAL PUBLIC-SOURCE FRONTIER
--
-- The acquired public report now pays:
--   * exact historical WC103 + VH-101 material/coating identity;
--   * nozzle extent/contour class and source-reported thermal-model validation;
--   * a near-matched 2300 F Haynes-damage / WC103-survival discriminator;
--   * proof that temperature-only and material-blind monotone-duration models
--     cannot fit both outcomes;
--   * proof that missing local wall thickness makes thin-shell stress
--     non-unique even at fixed pressure-radius load.
--
-- The remaining calibrated prediction is therefore an EXTERNAL producer problem,
-- not another abstract formalisation problem.
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

-- Literal reuse receipts ensure this terminal owner stays attached to the
-- already-paid producers rather than restating them as prose-only claims.
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
