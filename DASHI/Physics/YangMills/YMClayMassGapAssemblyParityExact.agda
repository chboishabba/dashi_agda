{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YMClayMassGapAssemblyParityExact where

------------------------------------------------------------------------
-- AGDA PARITY FOR LEAN RequestProject.YangMills.Clay.MassGapAssembly
--
-- Lean exposes two finite-gap producers (energy-form and source/clustering)
-- feeding one common cutoff->continuum->OS spine.  This Agda owner mirrors that
-- consumer topology and keeps all literal physical inputs visible.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.YMClayBoundedFormParityExact as Form

record MassGapConclusion
    (ContinuumHamiltonian Vacuum GapParameter : Set) : Set₁ where
  field
    hamiltonian : ContinuumHamiltonian
    vacuum : Vacuum
    gap : GapParameter

    GapPositive : Set
    gapPositive : GapPositive

    VacuumFormGap : Set
    vacuumFormGap : VacuumFormGap

    NoPositiveSubgapMode : Set
    noPositiveSubgapMode : NoPositiveSubgapMode

    VacuumSectorResolvent : Set
    vacuumSectorResolvent : VacuumSectorResolvent

open MassGapConclusion public

-- Finite gap evidence lives in Set₁ in both active routes (the concrete source
-- route uses Gap.PositiveTransferGapCore; the form route uses
-- Form.FiniteVacuumFormGapDatum), so the common route is universe-correct at
-- Set₂ instead of erasing the proof object to a Bool/token.
record CommonContinuumOSRoute
    (FiniteGap : Set₁)
    (ContinuumGap ContinuumHamiltonian Vacuum GapParameter : Set) : Set₂ where
  field
    cutoffToContinuum : FiniteGap → ContinuumGap
    ymOSSameObject : ContinuumGap →
      MassGapConclusion ContinuumHamiltonian Vacuum GapParameter

open CommonContinuumOSRoute public

commonContinuumOSCompiler :
  ∀ {FiniteGap : Set₁}
    {ContinuumGap ContinuumHamiltonian Vacuum GapParameter : Set} →
  CommonContinuumOSRoute
    FiniteGap ContinuumGap ContinuumHamiltonian Vacuum GapParameter →
  FiniteGap →
  MassGapConclusion ContinuumHamiltonian Vacuum GapParameter
commonContinuumOSCompiler route finiteGap =
  ymOSSameObject route (cutoffToContinuum route finiteGap)

record EnergyFormRoute
    (Hilbert Scalar : Set) : Set₁ where
  field
    finiteForms : Form.BoundedFormGapPackage Hilbert Scalar

open EnergyFormRoute public

finiteGapOfEnergyForms :
  ∀ {Hilbert Scalar} →
  EnergyFormRoute Hilbert Scalar →
  Form.FiniteVacuumFormGapDatum Hilbert Scalar
finiteGapOfEnergyForms route =
  Form.boundedFormBuildsFiniteVacuumGapDatum (finiteForms route)

record SourceClusteringRoute
    (SpectralRepresentation CovarianceDecay : Set)
    (FiniteGap : Set₁) : Set₂ where
  field
    spectralRepresentation : SpectralRepresentation
    covarianceDecay : CovarianceDecay
    clusteringGapCompiler :
      SpectralRepresentation → CovarianceDecay → FiniteGap

open SourceClusteringRoute public

finiteGapOfSourceClustering :
  ∀ {SpectralRepresentation CovarianceDecay : Set}
    {FiniteGap : Set₁} →
  SourceClusteringRoute SpectralRepresentation CovarianceDecay FiniteGap →
  FiniteGap
finiteGapOfSourceClustering route =
  clusteringGapCompiler route
    (spectralRepresentation route)
    (covarianceDecay route)

massGapOfEnergyForms :
  ∀ {Hilbert Scalar ContinuumGap ContinuumHamiltonian Vacuum GapParameter} →
  EnergyFormRoute Hilbert Scalar →
  CommonContinuumOSRoute
    (Form.FiniteVacuumFormGapDatum Hilbert Scalar)
    ContinuumGap ContinuumHamiltonian Vacuum GapParameter →
  MassGapConclusion ContinuumHamiltonian Vacuum GapParameter
massGapOfEnergyForms energy common =
  commonContinuumOSCompiler common (finiteGapOfEnergyForms energy)

massGapOfSourceClustering :
  ∀ {SpectralRepresentation CovarianceDecay : Set}
    {FiniteGap : Set₁}
    {ContinuumGap ContinuumHamiltonian Vacuum GapParameter : Set} →
  SourceClusteringRoute SpectralRepresentation CovarianceDecay FiniteGap →
  CommonContinuumOSRoute
    FiniteGap ContinuumGap ContinuumHamiltonian Vacuum GapParameter →
  MassGapConclusion ContinuumHamiltonian Vacuum GapParameter
massGapOfSourceClustering source common =
  commonContinuumOSCompiler common (finiteGapOfSourceClustering source)

data EnergyAssemblerPresent : Set where
  energyAssemblerPresent : EnergyAssemblerPresent

data SourceAssemblerPresent : Set where
  sourceAssemblerPresent : SourceAssemblerPresent

energyAssemblerWitness : EnergyAssemblerPresent
energyAssemblerWitness = energyAssemblerPresent

sourceAssemblerWitness : SourceAssemblerPresent
sourceAssemblerWitness = sourceAssemblerPresent

massGapAssemblyParityCompilerLevel : ProofLevel
massGapAssemblyParityCompilerLevel = machineChecked

energyFormToFiniteGapMathematicsLevel : ProofLevel
energyFormToFiniteGapMathematicsLevel = machineChecked

sourceClusteringToFiniteGapMathematicsLevel : ProofLevel
sourceClusteringToFiniteGapMathematicsLevel = conditional

physicalCutoffToContinuumInputsLevel : ProofLevel
physicalCutoffToContinuumInputsLevel = conditional

physicalYMOSSameObjectInputsLevel : ProofLevel
physicalYMOSSameObjectInputsLevel = conditional

massGapAssemblyParityImplemented : Bool
massGapAssemblyParityImplemented = true

massGapAssemblyParityImplementedIsTrue :
  massGapAssemblyParityImplemented ≡ true
massGapAssemblyParityImplementedIsTrue = refl

unconditionalClayPromotion : Bool
unconditionalClayPromotion = false

unconditionalClayPromotionIsFalse : unconditionalClayPromotion ≡ false
unconditionalClayPromotionIsFalse = refl
