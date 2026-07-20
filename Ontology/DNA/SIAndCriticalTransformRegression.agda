module Ontology.DNA.SIAndCriticalTransformRegression where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

open import DASHI.Physics.Units.SI using
  ( Dimension; Length; Mass; Time; Energy; MolarEnergy; MolarEntropy
  ; Unit; metre; kilogram; second; joule; joulePerMole; joulePerMoleKelvin
  ; Quantity; deciScale; centiScale
  )
open import Ontology.DNA.SantaLucia1998SI using
  ( unified1998SI; AA-TT-H-SI; GC-CG-G-SI )
open import Ontology.DNA.CriticallySampledDNA4Transform using
  ( coefficientCount; coefficientCount-is-256
  ; synthesise4-analyse4; criticalSamplingReceipt )

lengthUnitWellTyped : Unit Length
lengthUnitWellTyped = metre

massUnitWellTyped : Unit Mass
massUnitWellTyped = kilogram

timeUnitWellTyped : Unit Time
timeUnitWellTyped = second

energyUnitWellTyped : Unit Energy
energyUnitWellTyped = joule

molarEnergyUnitWellTyped : Unit MolarEnergy
molarEnergyUnitWellTyped = joulePerMole

molarEntropyUnitWellTyped : Unit MolarEntropy
molarEntropyUnitWellTyped = joulePerMoleKelvin

criticalCountRegression : coefficientCount ≡ 256
criticalCountRegression = coefficientCount-is-256
