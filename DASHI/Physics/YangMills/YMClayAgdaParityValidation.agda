{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YMClayAgdaParityValidation where

-- RED/GREEN parity surface for the retained Lean RequestProject.YangMills.Clay
-- tranche.  The production owners imported below must expose the same two
-- consumer routes: bounded physical energy form and source/clustering, both
-- entering one common continuum/OS mass-gap conclusion.

import DASHI.Physics.YangMills.YMClayBoundedFormParityExact as Form
import DASHI.Physics.YangMills.YMClayMassGapAssemblyParityExact as Assembly

open Form
open Assembly

boundedFormPackageAvailable : ∀ Hilbert Scalar → Set₁
boundedFormPackageAvailable = BoundedFormGapPackage

massGapConclusionAvailable :
  ∀ ContinuumHamiltonian Vacuum GapParameter → Set₁
massGapConclusionAvailable = MassGapConclusion

energyFormRouteAvailable : ∀ Hilbert Scalar FiniteGap → Set₁
energyFormRouteAvailable = EnergyFormRoute

sourceRouteAvailable :
  ∀ SpectralRepresentation CovarianceDecay FiniteGap → Set₁
sourceRouteAvailable = SourceClusteringRoute

commonContinuumRouteAvailable :
  ∀ FiniteGap ContinuumGap ContinuumHamiltonian Vacuum GapParameter → Set₁
commonContinuumRouteAvailable = CommonContinuumOSRoute

-- The validation surface intentionally names the two headline assemblers.
energyAssemblerIsPresent : Set
energyAssemblerIsPresent = EnergyAssemblerPresent

sourceAssemblerIsPresent : Set
sourceAssemblerIsPresent = SourceAssemblerPresent

energyAssemblerWitnessAvailable : EnergyAssemblerPresent
energyAssemblerWitnessAvailable = energyAssemblerWitness

sourceAssemblerWitnessAvailable : SourceAssemblerPresent
sourceAssemblerWitnessAvailable = sourceAssemblerWitness
