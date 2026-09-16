module DASHI.Environment.ElectricalPumpWaterServicePrimarySourceExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.ScientificWorkAttributionExact as Attribution

------------------------------------------------------------------------
-- PRIMARY INSTITUTIONAL ELECTRICAL-PUMP / WATER-SERVICE SOURCES
--
-- Attribution invariant:
-- institutional measurement guidance or operational case record
-- != DASHI matched-service weld != gravity displacement theorem
-- != lifecycle-energy recommendation.
------------------------------------------------------------------------

data ElectricalPumpSourceRole : Set where
  measurementProtocol
  operationalFieldCase : ElectricalPumpSourceRole

record ElectricalPumpPrimarySource : Set where
  constructor electrical-pump-primary-source
  field
    institution : String
    title : String
    year : Nat
    identifier : String
    sourceRole : ElectricalPumpSourceRole
    boundedReading : String
    excludedPromotion : String
    sourceStrength : Attribution.SourceStrength
    claimOwner : Attribution.ClaimOwner

open ElectricalPumpPrimarySource public

agricultureVictoriaPivotEnergyProtocol : ElectricalPumpPrimarySource
agricultureVictoriaPivotEnergyProtocol = electrical-pump-primary-source
  "Agriculture Victoria"
  "Centre pivot performance check"
  2020
  "Agriculture Victoria institutional guidance; page updated 19 June 2020"
  measurementProtocol
  "For electric irrigation systems, the guidance instructs measuring electricity-meter consumption and flow-meter volume across an irrigation event and reporting kWh per ML; total operating head and pump/motor efficiency remain relevant."
  "Does not establish the energy use of an unmeasured installation, does not prove gravity displacement, and does not turn a benchmark value into an exact site measurement."
  Attribution.primaryInstitutionalRecord
  Attribution.externalSourceOwner

queenslandSunshineCoastDairyEnergyCase : ElectricalPumpPrimarySource
queenslandSunshineCoastDairyEnergyCase = electrical-pump-primary-source
  "Queensland Farmers' Federation / Ag Energy Hub"
  "Sunshine Coast Dairy Farm"
  2026
  "Ag Energy Hub Energy Savers Plus Extension operational case record"
  operationalFieldCase
  "The institutional case record reports measured/retained pre- and post-implementation electricity consumption and irrigation distribution performance for the farm after pump/system changes."
  "Does not establish a universal pump-efficiency intervention effect, does not match the Krameterhof/Keyline gravity service by itself, and does not pay lifecycle energy or ecological outcome."
  Attribution.primaryInstitutionalRecord
  Attribution.externalSourceOwner

------------------------------------------------------------------------
-- WrongType / attribution barriers.
------------------------------------------------------------------------

data MeterProtocolMeansSiteMeasurementPermission : Set where
data OperationalCaseMeansUniversalSavingPermission : Set where
data ElectricalEnergyMeansHydraulicEnergyPermission : Set where
data PrimaryInstitutionOwnsDashiWeldPermission : Set where

guidanceDoesNotManufactureSiteMeasurement :
  MeterProtocolMeansSiteMeasurementPermission → ⊥
guidanceDoesNotManufactureSiteMeasurement ()

operationalCaseDoesNotUniversaliseSaving :
  OperationalCaseMeansUniversalSavingPermission → ⊥
operationalCaseDoesNotUniversaliseSaving ()

electricalEnergyDoesNotEqualHydraulicEnergy :
  ElectricalEnergyMeansHydraulicEnergyPermission → ⊥
electricalEnergyDoesNotEqualHydraulicEnergy ()

primaryInstitutionDoesNotOwnDashiWeld :
  PrimaryInstitutionOwnsDashiWeldPermission → ⊥
primaryInstitutionDoesNotOwnDashiWeld ()

record ElectricalPumpSourceBoundary : Set where
  constructor electrical-pump-source-boundary
  field
    protocolAndMeasurementRemainDistinct : Bool
    hydraulicAndElectricalEnergyRemainDistinct : Bool
    sourceAndDashiWeldRemainDistinct : Bool
    operationalCaseAndTransportRemainDistinct : Bool
    sourceAutomaticallyProvesGravityDisplacement : Bool

canonicalElectricalPumpSourceBoundary : ElectricalPumpSourceBoundary
canonicalElectricalPumpSourceBoundary =
  electrical-pump-source-boundary true true true true false
