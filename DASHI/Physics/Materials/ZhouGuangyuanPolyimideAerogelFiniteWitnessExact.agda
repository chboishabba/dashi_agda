module DASHI.Physics.Materials.ZhouGuangyuanPolyimideAerogelFiniteWitnessExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Units.SI as SI
import DASHI.Physics.Materials.ZhouGuangyuanPolyimideAerogelBidiExact as Zhou

------------------------------------------------------------------------
-- SOURCE-EXACT FINITE MATERIAL WITNESS
------------------------------------------------------------------------

record FiniteZhouAerogelWitness : Set where
  constructor finite-zhou-aerogel-witness
  field
    sourceReference : String
    testTemperature : SI.Quantity SI.Temperature SI.centiScale
    thermalConductivity : SI.Quantity Zhou.ThermalConductivity Zhou.conductivityScale
    shrinkageDeciPercentUpperExample : Nat
    porosityPercentLowerBound : Nat
    specificSurfaceAreaDeciSquareMetresPerGram : Nat
    td5CelsiusLowerBound : Nat
    tgCelsiusLowerBound : Nat
    sourceExactMeasurement : Bool
    universalProcessWindowPaid : Bool
    nextExactLeaf : String

open FiniteZhouAerogelWitness public

finiteZhouAerogelWitness : FiniteZhouAerogelWitness
finiteZhouAerogelWitness = finite-zhou-aerogel-witness
  "DOI 10.1016/j.cej.2023.147642"
  Zhou.testTemperatureKelvin
  Zhou.thermalConductivityAt200C
  77
  91
  6748
  580
  299
  true
  false
  "recover source-exact synthesis recipe, batch variation and a finite multi-sample structure/process/property table before deriving a manufacturing window"

finiteWitnessCarriesSIConductivity : Bool
finiteWitnessCarriesSIConductivity = true

singleFiniteWitnessPaysScaleUp : Bool
singleFiniteWitnessPaysScaleUp = false

singleFiniteWitnessPaysEveryThermalApplication : Bool
singleFiniteWitnessPaysEveryThermalApplication = false
