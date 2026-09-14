module DASHI.Culture.MissingDeceasedCombinedRocketScramjetVehicleBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)

import DASHI.Core.ApplicationTransformationCapabilityBidiExact as T
import DASHI.Core.RealObjectApplicationBidiExact as R
import DASHI.Culture.MissingDeceasedHypersonicAirbreathingVehicleBidiExact as Hyp

------------------------------------------------------------------------
-- COMBINED BOOSTER-ROCKET + AIRBREATHING RESEARCH VEHICLE
--
-- One vehicle architecture may contain a stored-oxidizer rocket booster and a
-- later atmospheric-air-breathing hypersonic stage.  They remain distinct
-- thermodynamic objects even when integrated by one vehicle.
------------------------------------------------------------------------

rocketFeedRequirement : R.RealObjectRequirement
rocketFeedRequirement = R.mkRequirement
  "booster rocket oxidizer/fuel system"
  "store, feed and burn rocket propellants across a qualified pressure/thermal/material envelope"
  "NASA liquid-rocket source retained in MissingDeceasedHypersonicAirbreathingVehicleBidiExact"
  (T.acquireConstitutiveConfiguration ∷ T.acquireOperatingWindow ∷ T.acquireFailureHistory ∷ T.acquireQualificationEvidence ∷ [])
  "Stored-oxidizer rocket qualification does not transfer automatically to atmospheric scramjet service."

scramjetFlowRequirement : R.RealObjectRequirement
scramjetFlowRequirement = R.mkRequirement
  "airbreathing hypersonic stage"
  "ingest atmospheric air, manage inlet/shock/SBLI state and sustain a vehicle-specific supersonic-combustion operating window"
  "NASA scramjet/inlet sources retained in MissingDeceasedHypersonicAirbreathingVehicleBidiExact"
  (T.acquireApplicationGeometry ∷ T.acquireOperatingWindow ∷ T.acquireValidationCorpus ∷ T.acquireQualificationEvidence ∷ [])
  "Inlet compression heats the flow and does not itself provide an air-liquefaction process."

commonVehicleRequirement : R.RealObjectRequirement
commonVehicleRequirement = R.mkRequirement
  "common vehicle integration"
  "integrate structures, thermal management, sensing, fault tolerance, hardware verification, guidance and staged transition"
  "generic vehicle-level integration boundary"
  (T.acquireApplicationGeometry ∷ T.acquireIntegrationWorkflow ∷ T.acquireFailureHistory ∷ T.acquireQualificationEvidence ∷ [])
  "Subsystem compatibility does not establish a historical integrated vehicle or programme."

boosterRocketObject : R.RealEngineeringObject
boosterRocketObject = R.real-engineering-object
  "stored-oxidizer booster rocket research stage"
  "benign propulsion research object"
  Hyp.hypersonicSourceAtlas
  (rocketFeedRequirement ∷ commonVehicleRequirement ∷ [])
  "accelerate a research vehicle and study rocket-side oxygen-service/material/control requirements"
  "This object is a design-space consumer of retained science, not evidence of a historical common programme."

airbreathingObject : R.RealEngineeringObject
airbreathingObject = R.real-engineering-object
  "airbreathing scramjet research stage"
  "benign hypersonic propulsion research object"
  Hyp.hypersonicSourceAtlas
  (scramjetFlowRequirement ∷ commonVehicleRequirement ∷ [])
  "study atmospheric hypersonic inlet/combustion/control integration"
  "This object remains thermodynamically distinct from the stored-oxidizer booster stage."

commonVehicleObject : R.RealEngineeringObject
commonVehicleObject = R.real-engineering-object
  "combined rocket-boost plus scramjet-cruise research vehicle"
  "staged benign aerospace research vehicle"
  Hyp.hypersonicSourceAtlas
  (rocketFeedRequirement ∷ scramjetFlowRequirement ∷ commonVehicleRequirement ∷ [])
  "study staged propulsion transition and common vehicle integration"
  "A possible integrated engineering architecture does not create historical collaboration, H2, H3 or event cause."

rezaBoosterFit : R.ScientistObjectFit
rezaBoosterFit = R.mkFit
  "Monica Jacinto / Monica Reza"
  "DASHI.Physics.Materials.RezaBurnResistantAlloyBidiExact"
  "high-pressure oxygen-service burn-resistant alloy/process lineage"
  rocketFeedRequirement R.directSourceFit
  "Jacinto/Hardwick burn-resistant alloy patent family and downstream MONDALOY rocket oxygen-service lineage"
  "The retained alloy is directly motivated by severe oxygen-service materials problems on the rocket side."
  "recover exact component/process window and subsystem qualification for the proposed booster application"
  false
  "Direct application lineage does not establish participation in this combined vehicle."

yanAirbreathingFit : R.ScientistObjectFit
yanAirbreathingFit = R.mkFit
  "Yan Hong"
  "DASHI.Physics.Aerospace.YanHongHypersonicFlowControlBidiExact"
  "Mach-5 inlet thermal excitation / shock-boundary-layer control"
  scramjetFlowRequirement R.directSourceFit
  "DOI 10.7638/kqdlxxb-2013.0102"
  "The retained work is itself a hypersonic inlet control study and fits the airbreathing side directly."
  "recover exact response curves, source model, geometry and integrated-stage qualification"
  false
  "Direct technical fit does not identify a historical vehicle."

mccaslandCommonVehicleFit : R.ScientistObjectFit
mccaslandCommonVehicleFit = R.mkFit
  "William Neil McCasland"
  "DASHI.Control.McCaslandFaultTolerantFlexibleStructureControlBidiExact"
  "fault-tolerant sensor/actuator placement"
  commonVehicleRequirement R.methodTransfer
  "McCasland 1989 fault-tolerant placement work"
  "The control method can transfer to a vehicle-specific state-space model and failure family."
  "supply vehicle model, candidate sites, failure set and integrated qualification evidence"
  false
  "Method transfer does not pay deployed implementation or programme membership."

rocketOxidizerAndScramjetAirAreDifferentInputs : Bool
rocketOxidizerAndScramjetAirAreDifferentInputs = true

rocketBoostAndScramjetCruiseCanShareVehicle : Bool
rocketBoostAndScramjetCruiseCanShareVehicle = true

inletCompressionPaysAirLiquefaction : Bool
inletCompressionPaysAirLiquefaction = false

rocketAndScramjetAreSameThermodynamicObject : Bool
rocketAndScramjetAreSameThermodynamicObject = false

combinedVehicleFitPaysHistoricalProgramme : Bool
combinedVehicleFitPaysHistoricalProgramme = false
