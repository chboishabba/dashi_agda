{-# OPTIONS --safe #-}
module DASHI.Quantum.QuantumBirthmarkFiniteVacuumStressExact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
import Data.Integer.Base as Int
open import Data.Rational.Base using (_/_; -_)

import DASHI.Geometry.FlatLorentzianModel as Flat
import DASHI.Physics.Foundations.GRQFTRationalStressComponentCutExact as Stress
import DASHI.Physics.Foundations.GRQFTVacuumStressLambdaCompilerExact as Vacuum
import DASHI.Quantum.QuantumBirthmarkCommonHistoryIdentityBenchmarkExact as Birthmark
import DASHI.Quantum.QuantumBirthmarkFiniteOrderParameterCouplingExact as Coupling

birthmarkVacuumStress :
  Birthmark.BirthmarkClass → Stress.RationalTensor4
birthmarkVacuumStress birthmark =
  Vacuum.vacuumStressAt (Coupling.birthmarkVacuumEnergy birthmark)

lowBirthmarkStress00 :
  birthmarkVacuumStress Birthmark.lowBirthmark Flat.timeAxis Flat.timeAxis
  ≡ Int.+ 21 / 64
lowBirthmarkStress00 = refl

lowBirthmarkStress11 :
  birthmarkVacuumStress Birthmark.lowBirthmark Flat.xAxis Flat.xAxis
  ≡ - (Int.+ 21 / 64)
lowBirthmarkStress11 = refl

highBirthmarkStress00 :
  birthmarkVacuumStress Birthmark.highBirthmark Flat.timeAxis Flat.timeAxis
  ≡ Int.+ 3 / 8
highBirthmarkStress00 = refl

highBirthmarkStress11 :
  birthmarkVacuumStress Birthmark.highBirthmark Flat.xAxis Flat.xAxis
  ≡ - (Int.+ 3 / 8)
highBirthmarkStress11 = refl

finiteBirthmarkToVacuumStressOwned : Bool
finiteBirthmarkToVacuumStressOwned = true

finiteBirthmarkAmplitudeCompilesToEffectiveLambda : Bool
finiteBirthmarkAmplitudeCompilesToEffectiveLambda = true

sourceNativeMetricVariationStillRequired : Bool
sourceNativeMetricVariationStillRequired = true

finiteStressModelIsNotPRXEmpiricalGravityResult : Bool
finiteStressModelIsNotPRXEmpiricalGravityResult = true
