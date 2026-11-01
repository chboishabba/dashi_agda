module DASHI.Physics.Materials.ZhouGuangyuanAerogelProcessPropertyDataReplayExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Materials.ZhouGuangyuanPolyimideAerogelBidiExact as Base

------------------------------------------------------------------------
-- ZHOU GUANGYUAN / PI-AEROGEL SOURCE-DATA REPLAY
-- DOI 10.1016/j.cej.2023.147642.
-- Public publisher abstract/highlights expose two named samples and selected
-- process/property coordinates.  They do not expose the complete sample table.
------------------------------------------------------------------------

record ZhouProcessPropertyDataReplay : Set where
  constructor zhou-process-property-data-replay
  field
    sourceReference : String
    highestAreaSample : String
    highestAreaTenthsM2PerG : Nat
    insulationSample : String
    bdfaToOdaRatio : String
    conductivityTenthsMilliWPerMPerKAt200C : Nat
    shrinkageTenthsPercent : Nat
    poreSizeNmApprox : Nat
    td5LowerBoundC : Nat
    tgLowerBoundC : Nat
    completeSampleTablePaid : Bool
    scaleUpProcessWindowPaid : Bool

open ZhouProcessPropertyDataReplay public

zhouProcessPropertyDataReplay : ZhouProcessPropertyDataReplay
zhouProcessPropertyDataReplay = zhou-process-property-data-replay
  "DOI 10.1016/j.cej.2023.147642"
  "PI-D1, composed entirely of BDFD"
  6748
  "PI-A4"
  "BDFA/ODA molar ratio 1/3"
  543
  77
  24
  580
  299
  false
  false

existingAerogelState : Base.PolyimideAerogelState
existingAerogelState = Base.canonicalZhouAerogelState

sourceDataReplayPaysNamedSamples : Bool
sourceDataReplayPaysNamedSamples = true

sourceDataReplayPaysPIA4ProcessPropertyCoordinates : Bool
sourceDataReplayPaysPIA4ProcessPropertyCoordinates = true

sourceDataReplayPaysFullManufacturingWindow : Bool
sourceDataReplayPaysFullManufacturingWindow = false
