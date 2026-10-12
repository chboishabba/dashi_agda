{-# OPTIONS --safe #-}
module DASHI.Physics.Materials.RocketdyneMaterialSurvivabilityCrossPollinationExact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Propulsion.Rocketdyne1974MaterialIdentityAndConstitutiveDataExact as Mat
import DASHI.Physics.Propulsion.Rocketdyne1974TwoMaterialDiscriminatorExact as Disc
import DASHI.Physics.Propulsion.Rocketdyne1974IdentifiabilityCutExact as Cut
import DASHI.Physics.Propulsion.Rocketdyne1974ThermalModelValidationExact as Therm
import DASHI.Physics.Propulsion.Rocketdyne1974MaterialDependentThermalFalsifierExact as Fals
import DASHI.Physics.Propulsion.Rocketdyne1974TerminalPhysicalFrontierExact as Terminal
import DASHI.Physics.Propulsion.Rocketdyne1974FlightC103ManufacturingLessonExact as FlightC103
import DASHI.Physics.Materials.FusionPropulsionMaterialSurvivabilityCrossPollinationExact as FusionMat
import DASHI.Physics.Materials.RezaBurnResistantAlloyBidiExact as Reza

------------------------------------------------------------------------
-- MATERIAL-SURVIVABILITY CROSS-POLLINATION
--
-- The transferable grammar is now intentionally richer than
--   environment -> material -> temperature -> outcome.
-- Later Shuttle C-103 flight experience independently demonstrates that
-- process history, surface state, chemical exposure, residual/applied stress
-- and inspection observability can be decisive coordinates.  That later root
-- cause is NOT transferred back to the 1974 Rocketdyne article.
------------------------------------------------------------------------

record SurvivabilityTransfer : Set where
  constructor survivability-transfer
  field
    sourceCase : String
    destinationLane : String
    transferableMethod : String
    sameMaterialSystem : Bool
    sameHistoricalProgramme : Bool
    exactEnvironmentTransferPaid : Bool
    remainingPayment : String

rocketdyneToReza : SurvivabilityTransfer
rocketdyneToReza = survivability-transfer
  "1974 Haynes-25 / WC103 nozzle comparison + later Shuttle C-103 process-history lesson"
  "Reza/Jacinto/Hardwick oxygen-rich chemical-rocket materials"
  "keep environment, material/coating, manufacturing history, geometry/load/exposure, inspection and observed outcome as separate coordinates"
  false false false
  "pay oxygen compatibility, alloy microstructure/process history, pressure/temperature history, inspection and same-object qualification separately"

rocketdyneToFusion : SurvivabilityTransfer
rocketdyneToFusion = survivability-transfer
  "1974 chemical-rocket discriminator + later C-103 manufacturing/NDE lesson"
  "fusion-propulsion material survivability"
  "reuse provenance, source-validated thermal-model, same-model discrimination, process-history and inspection discipline"
  false false false
  "plasma radiation, magnetic loading, neutron/ion damage, thermal environment, fabrication route and inspection acceptance are distinct producers"

existingFusionMaterialBoundary : FusionMat.FusionMaterialBoundary
existingFusionMaterialBoundary = FusionMat.canonicalFusionMaterialBoundary

existingRezaBoundary : Reza.RezaAlloyBoundary
existingRezaBoundary = Reza.canonicalRezaAlloyBoundary

rocketdyneEmpiricalDiscriminator : Disc.TwoMaterialDiscriminator
rocketdyneEmpiricalDiscriminator = Disc.currentDiscriminator

rocketdyneIdentifiabilityCut : Cut.PhysicalMaxCut
rocketdyneIdentifiabilityCut = Cut.currentPhysicalMaxCut

rocketdyneThermalValidation : Therm.ThermalModelBoundary
rocketdyneThermalValidation = Therm.canonicalThermalModelBoundary

rocketdyneMaterialDependence : Fals.MaterialDependenceBoundary
rocketdyneMaterialDependence = Fals.canonicalMaterialDependenceBoundary

rocketdyneTerminalFrontier : Terminal.TerminalPhysicalFrontier
rocketdyneTerminalFrontier = Terminal.currentTerminalFrontier

flightC103ManufacturingLesson : FlightC103.FlightC103CrackingLesson
flightC103ManufacturingLesson = FlightC103.shuttleC103CrackingLesson

manufacturingProcessCoordinateRequired : Bool
manufacturingProcessCoordinateRequired = true

record CrossPollinationBoundary : Set where
  constructor cross-pollination-boundary
  field
    sharedSurvivabilityGrammar : Bool
    sharedGrammarImpliesSameMaterial : Bool
    sharedGrammarImpliesSameProgramme : Bool
    historicalDiscriminatorMayConstrainMethod : Bool
    temperatureOnlySurvivabilityModelIsAdequate : Bool
    materialIdentityAloneIsAdequate : Bool
    manufacturingProcessAndInspectionAreLiveCoordinates : Bool
    laterFlightRootCauseTransfersTo1974 : Bool
    destinationStillNeedsOwnValidation : Bool

canonicalCrossPollinationBoundary : CrossPollinationBoundary
canonicalCrossPollinationBoundary =
  cross-pollination-boundary true false false true false false true false true
