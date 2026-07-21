module DASHI.Physics.Closure.NSPeriodicConcreteMultiplierScalingReceipt where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

------------------------------------------------------------------------
-- Exact status mirror of the radial max-norm hat scale regression.
------------------------------------------------------------------------

shellRadiusPairsChecked : Nat
shellRadiusPairsChecked = 51

radiusOneGainDenominator radiusTwoGainDenominator : Nat
radiusOneGainDenominator = 1
radiusTwoGainDenominator = 2

radiusThreeGainDenominator radiusFourGainDenominator : Nat
radiusThreeGainDenominator = 4
radiusFourGainDenominator = 8

radiusFiveGainDenominator radiusSixGainDenominator : Nat
radiusFiveGainDenominator = 16
radiusSixGainDenominator = 32

radiusSevenGainDenominator radiusEightGainDenominator : Nat
radiusSevenGainDenominator = 64
radiusEightGainDenominator = 128

allRadialRowsScaleInvariant : Bool
allRadialRowsScaleInvariant = true

radiusEightScalingRegression : radiusEightGainDenominator ≡ 128
radiusEightScalingRegression = refl

radialMultiplierScalingProvesFullOperatorBound : Bool
radialMultiplierScalingProvesFullOperatorBound = false

cutoffUniformFullFarLowProved : Bool
cutoffUniformFullFarLowProved = false
