module DASHI.Biology.DNAChemistryEnergyAlgebra where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Data.List.Base using (List; []; _∷_)

import DASHI.Biology.DNAChemistryCarrier as DNA

isGC : DNA.DNABase → Nat
isGC DNA.A = zero
isGC DNA.T = zero
isGC DNA.C = suc zero
isGC DNA.G = suc zero

gcCount : List DNA.DNABase → Nat
gcCount [] = zero
gcCount (b ∷ bs) = isGC b + gcCount bs

record ExactConstraintEnergy : Set where
  constructor exactEnergy
  field
    gcPenalty : Nat
    runPenalty : Nat
    motifPenalty : Nat
open ExactConstraintEnergy public

record OperationalThermoEnergy : Set where
  constructor thermoEnergy
  field
    nearestNeighbourScore : Nat
    hairpinScore : Nat
    dimerScore : Nat
    saltTemperatureCorrection : Nat
open OperationalThermoEnergy public

record EnergyWeights : Set where
  constructor weights
  field
    λGC λRun λMotif λNN λHairpin λDimer λEnvironment : Nat
open EnergyWeights public

weightedExact : EnergyWeights → ExactConstraintEnergy → Nat
weightedExact w e =
  λGC w * gcPenalty e
  + λRun w * runPenalty e
  + λMotif w * motifPenalty e

weightedOperational : EnergyWeights → OperationalThermoEnergy → Nat
weightedOperational w e =
  λNN w * nearestNeighbourScore e
  + λHairpin w * hairpinScore e
  + λDimer w * dimerScore e
  + λEnvironment w * saltTemperatureCorrection e

totalHamiltonian :
  EnergyWeights → ExactConstraintEnergy → OperationalThermoEnergy → Nat
totalHamiltonian w exact operational =
  weightedExact w exact + weightedOperational w operational

record OperationalChemistryModel : Set₁ where
  constructor model
  field
    exactTerms : List DNA.DNABase → ExactConstraintEnergy
    thermoTerms : List DNA.DNABase → OperationalThermoEnergy
    modelWeights : EnergyWeights
open OperationalChemistryModel public

Hamiltonian : OperationalChemistryModel → List DNA.DNABase → Nat
Hamiltonian m xs = totalHamiltonian (modelWeights m) (exactTerms m xs) (thermoTerms m xs)

-- The following distinction is intentional:
-- exactTerms are exact relative to the formal codec predicates;
-- thermoTerms are exact evaluations of a supplied operational table/model;
-- adequacy to microscopic molecular chemistry is empirical, not proved here.
record EnergyAuthorityBoundary (m : OperationalChemistryModel) : Set where
  constructor authorityBoundary
  field
    exactCodecEvaluation : ∀ xs → Nat
    operationalModelEvaluation : ∀ xs → Nat
    completeQuantumHamiltonianRecovered : Set
open EnergyAuthorityBoundary public

canonicalZeroWeights : EnergyWeights
canonicalZeroWeights = weights zero zero zero zero zero zero zero

zeroExact : List DNA.DNABase → ExactConstraintEnergy
zeroExact xs = exactEnergy (gcCount xs) zero zero

zeroOperational : List DNA.DNABase → OperationalThermoEnergy
zeroOperational xs = thermoEnergy zero zero zero zero

canonicalOperationalModel : OperationalChemistryModel
canonicalOperationalModel = model zeroExact zeroOperational canonicalZeroWeights

canonicalHamiltonianIsZero : ∀ xs → Hamiltonian canonicalOperationalModel xs ≡ zero
canonicalHamiltonianIsZero xs = refl
