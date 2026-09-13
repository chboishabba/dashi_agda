module DASHI.Physics.Materials.FangDainingInverseDesignFiniteWitnessExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Materials.FangDainingActiveMechanicalMetamaterialBidiExact as F

record FiniteFangInverseDesignWitness : Set where
  constructor finite-fang-inverse-design-witness
  field
    sourceReference : String
    constructionPrinciples : List F.ConstructionPrinciple
    admissibleStimuli : List F.StimulusField
    finiteModeCount : Nat
    finiteWavevectorSamples : Nat
    negativeGroupVelocitySampleCount : Nat
    syntheticDispersionCarrier : Bool
    sourceDispersionReproduced : Bool
    nextExactLeaf : String

open FiniteFangInverseDesignWitness public

finiteFangInverseDesignWitness : FiniteFangInverseDesignWitness
finiteFangInverseDesignWitness = finite-fang-inverse-design-witness
  "DOI 10.1016/j.jmps.2025.106144; BIT active-mechanical-metamaterial research surface"
  (F.phaseTransition ∷ F.strainMismatch ∷ F.mechanicalInstability ∷ [])
  (F.temperature ∷ F.chemical ∷ F.light ∷ F.electric ∷ F.magnetic ∷ F.pressure ∷ [])
  2
  5
  1
  true
  false
  "recover the source energy functional, prescribed mode constraints, dispersion samples and experimental geometry, then replace this synthetic finite carrier with a source-exact inverse-design witness"

finiteWitnessExercisesInverseDesignShape : Bool
finiteWitnessExercisesInverseDesignShape = true

finiteWitnessIsSourceBandStructureReplication : Bool
finiteWitnessIsSourceBandStructureReplication = false

finiteWitnessPaysExoticMaterialProvenance : Bool
finiteWitnessPaysExoticMaterialProvenance = false
