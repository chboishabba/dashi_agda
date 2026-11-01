module DASHI.Physics.Spectroscopy.MaiwaldActionSpectroscopyFiniteWitnessExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Spectroscopy.MaiwaldActionSpectroscopyBidiExact as M

record FiniteMaiwaldActionWitness : Set where
  constructor finite-maiwald-action-witness
  field
    sourceReference : String
    target : M.SpectralObject
    trapMinimumK : Nat
    trapMaximumK : Nat
    stages : List M.SpectralStage
    frequencyBins : List Nat
    fragmentYieldBins : List Nat
    syntheticSpectrum : Bool
    sourceSpectrumReproduced : Bool
    nextExactLeaf : String

open FiniteMaiwaldActionWitness public

finiteMaiwaldActionWitness : FiniteMaiwaldActionWitness
finiteMaiwaldActionWitness = finite-maiwald-action-witness
  "JPL FY23 SURP; DOI 10.1021/acs.jpca.4c03552"
  M.messengerTaggedComplex
  (M.ActionSpectroscopyExperiment.trapMinimumK M.maiwaldSURP)
  (M.ActionSpectroscopyExperiment.trapMaximumK M.maiwaldSURP)
  (M.ionise ∷ M.cryogenicTrap ∷ M.irradiate ∷ M.photodissociate ∷ M.detectFragments ∷ M.inferIdentity ∷ [])
  (100 ∷ 101 ∷ 102 ∷ 103 ∷ 104 ∷ [])
  (2 ∷ 5 ∷ 11 ∷ 6 ∷ 1 ∷ [])
  true
  false
  "replace synthetic bins with a source-exact tagged-ion action spectrum, calibration state and isomer-reference comparison"

finiteWitnessExercisesActionSpectrumShape : Bool
finiteWitnessExercisesActionSpectrumShape = true

finiteWitnessIsDirectAbsorptionSpectrum : Bool
finiteWitnessIsDirectAbsorptionSpectrum = false

finiteWitnessPaysBiosignatureOrigin : Bool
finiteWitnessPaysBiosignatureOrigin = false
