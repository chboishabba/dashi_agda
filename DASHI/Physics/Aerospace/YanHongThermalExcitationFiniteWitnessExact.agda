module DASHI.Physics.Aerospace.YanHongThermalExcitationFiniteWitnessExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Aerospace.YanHongHypersonicFlowControlBidiExact as Y

record FiniteYanThermalExcitationWitness : Set where
  constructor finite-yan-thermal-excitation-witness
  field
    sourceReference : String
    workObject : Y.YanHongFlowControlObject
    sourceMethod : String
    actuatorCount : Nat
    actuatorDistanceIndex : Nat
    heatReleaseIndex : Nat
    shockAngleResponseIndex : Nat
    separationResponseIndex : Nat
    syntheticParameterisation : Bool
    sourceNumericsReproduced : Bool
    nextExactLeaf : String

open FiniteYanThermalExcitationWitness public

finiteYanThermalExcitationWitness : FiniteYanThermalExcitationWitness
finiteYanThermalExcitationWitness = finite-yan-thermal-excitation-witness
  "DOI 10.7638/kqdlxxb-2013.0102"
  Y.thermalExcitationShockControl
  (Y.YanHongWorkReceipt.method Y.thermalExcitationMach5Receipt)
  2
  3
  4
  2
  1
  true
  false
  "recover source-exact heat-release power, actuator count/distance values and shock/separation responses, then replace the synthetic indices with a paper-level finite witness"

finiteWitnessExercisesThermalControlCoordinates : Bool
finiteWitnessExercisesThermalControlCoordinates = true

finiteWitnessIsSourceMach5Replication : Bool
finiteWitnessIsSourceMach5Replication = false

finiteWitnessImpliesExoticPropulsion : Bool
finiteWitnessImpliesExoticPropulsion = false
