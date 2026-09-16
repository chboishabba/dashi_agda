{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YMClayAgdaParityValidation where

-- RED/GREEN parity surface for the retained Lean RequestProject.YangMills.Clay
-- tranche.  The production owners below expose the same two finite routes and
-- one common cutoff/OS mass-gap conclusion, with proof objects retained at
-- their actual universe levels.

import DASHI.Physics.YangMills.YMClayBoundedFormParityExact as Form
import DASHI.Physics.YangMills.YMClayMassGapAssemblyParityExact as Assembly
import DASHI.Physics.YangMills.YMClayFullChainParityExact as Full

open Form
open Assembly
open Full

boundedFormPackageAvailable :
  ∀ (Hilbert Scalar : Set) → Set₁
boundedFormPackageAvailable = BoundedFormGapPackage

finiteVacuumGapDatumAvailable :
  ∀ (Hilbert Scalar : Set) → Set₁
finiteVacuumGapDatumAvailable = FiniteVacuumFormGapDatum

massGapConclusionAvailable :
  ∀ (ContinuumHamiltonian Vacuum GapParameter : Set) → Set₁
massGapConclusionAvailable = MassGapConclusion

energyFormRouteAvailable :
  ∀ (Hilbert Scalar : Set) → Set₁
energyFormRouteAvailable = EnergyFormRoute

sourceRouteAvailable :
  ∀ (SpectralRepresentation CovarianceDecay : Set)
    (FiniteGap : Set₁) → Set₂
sourceRouteAvailable = SourceClusteringRoute

commonContinuumRouteAvailable :
  ∀ (FiniteGap : Set₁)
    (ContinuumGap ContinuumHamiltonian Vacuum GapParameter : Set) → Set₂
commonContinuumRouteAvailable = CommonContinuumOSRoute

boundedFullChainAvailable :
  ∀ (Hilbert Scalar ContinuumGap ContinuumHamiltonian Vacuum GapParameter : Set) →
  Set₂
boundedFullChainAvailable = BoundedFormClayInputs

-- The validation surface intentionally names the two headline assemblers.
energyAssemblerIsPresent : Set
energyAssemblerIsPresent = EnergyAssemblerPresent

sourceAssemblerIsPresent : Set
sourceAssemblerIsPresent = SourceAssemblerPresent

energyAssemblerWitnessAvailable : EnergyAssemblerPresent
energyAssemblerWitnessAvailable = energyAssemblerWitness

sourceAssemblerWitnessAvailable : SourceAssemblerPresent
sourceAssemblerWitnessAvailable = sourceAssemblerWitness
