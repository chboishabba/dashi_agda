{-# OPTIONS --safe #-}
module DASHI.Quantum.QuantumBirthmarkVacuumEnergyDiscrepancyBoundaryExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

planckDensityOrderExponent : Nat
planckDensityOrderExponent = 96

observedDarkEnergyInverseOrderExponent : Nat
observedDarkEnergyInverseOrderExponent = 27

massDensityExponentGap : Nat
massDensityExponentGap =
  planckDensityOrderExponent + observedDarkEnergyInverseOrderExponent

massDensityExponentGapIs123 :
  massDensityExponentGap ≡ 123
massDensityExponentGapIs123 = refl

quotedOneHundredTwentyOrdersIsConventionDependent : Bool
quotedOneHundredTwentyOrdersIsConventionDependent = true

historyHorizonScalingAutomaticallyCancelsUVVacuumEnergy : Bool
historyHorizonScalingAutomaticallyCancelsUVVacuumEnergy = false

historySectorCanBeDefinedWithoutNaiveUVZeroPointSum : Bool
historySectorCanBeDefinedWithoutNaiveUVZeroPointSum = true

vacuumEnergyProblemSolvedByCurrentHistoryModel : Bool
vacuumEnergyProblemSolvedByCurrentHistoryModel = false

planckDensityReference : String
planckDensityReference =
  "Planck-density order follows from standard Planck units built from hbar, c and G; exact numerical comparison depends on convention and constants"

observedDarkEnergyDensityReference : String
observedDarkEnergyDensityReference =
  "PDG reference dark-energy mass density: 5.83(16)e-27 kg m^-3"
