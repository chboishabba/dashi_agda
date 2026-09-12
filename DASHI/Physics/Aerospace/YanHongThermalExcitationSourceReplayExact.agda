module DASHI.Physics.Aerospace.YanHongThermalExcitationSourceReplayExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Aerospace.YanHongHypersonicFlowControlBidiExact as Y

------------------------------------------------------------------------
-- SOURCE-EXACT REPLAY COORDINATES
-- Yan Hong, Wang Song, Acta Aerodynamica Sinica 32(6), 2014, 806-813,
-- DOI 10.7638/kqdlxxb-2013.0102.
-- Public full text abstract exposes the four Mach-5 numerical cases.
------------------------------------------------------------------------

record ThermalExcitationCase : Set where
  constructor thermal-excitation-case
  field
    heatPowerKW : Nat
    actuatorCount : Nat
    distanceToShockM : String

record YanThermalSourceReplay : Set where
  constructor yan-thermal-source-replay
  field
    sourceReference : String
    flowRegime : String
    case1 case2 case3 case4 : ThermalExcitationCase
    sourceConclusion : String
    powerEffect : String
    countEffect : String
    placementEffect : String
    exactShockAngleSeriesPaid : Bool
    exactSeparationAreaSeriesPaid : Bool

open ThermalExcitationCase public
open YanThermalSourceReplay public

sourceExactYanThermalReplay : YanThermalSourceReplay
sourceExactYanThermalReplay = yan-thermal-source-replay
  "DOI 10.7638/kqdlxxb-2013.0102"
  "Mach 5 supersonic inlet, unsteady Navier-Stokes numerical study"
  (thermal-excitation-case 2 2 "0.02")
  (thermal-excitation-case 3 2 "0.02")
  (thermal-excitation-case 2 3 "0.02")
  (thermal-excitation-case 2 2 "0")
  "all four cases report significant thermal-excitation influence on shock control and shock-induced boundary-layer separation"
  "within the studied range, greater heat-release power produced larger original-shock-angle change and more evident separation-region change"
  "larger actuator count increases energy density; the near-wall shock surface becomes flatter and the separation-region size changes"
  "S=0.02 m gave effective control while S=0 m produced almost no flow-field change, indicating upstream placement is required in this setup"
  false
  false

existingWorkReceipt : Y.YanHongWorkReceipt
existingWorkReceipt = Y.thermalExcitationMach5Receipt

case1Literal : String
case1Literal = "E=2 kW, N=2, S=0.02 m"

sourceReplayPaysFourCaseCoordinates : Bool
sourceReplayPaysFourCaseCoordinates = true

sourceReplayPaysExactResponseCurves : Bool
sourceReplayPaysExactResponseCurves = false

sourceReplayPaysOperationalVehicleDesign : Bool
sourceReplayPaysOperationalVehicleDesign = false
