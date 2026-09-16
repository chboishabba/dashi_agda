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

record CommonContinuumOSRoute
    (FiniteGap ContinuumGap ContinuumHamiltonian Vacuum GapParameter : Set) : Set₁ where
  field
    cutoffToContinuum : FiniteGap → ContinuumGap
    ymOSSameObject : ContinuumGap →
      MassGapConclusion ContinuumHamiltonian Vacuum GapParameter

open CommonContinuumOSRoute public

commonContinuumOSCompiler :
  ∀ {FiniteGap ContinuumGap ContinuumHamiltonian Vacuum GapParameter} →
  CommonContinuumOSRoute
    FiniteGap ContinuumGap ContinuumHamiltonian Vacuum GapParameter →
  FiniteGap →
  MassGapConclusion ContinuumHamiltonian Vacuum GapParameter
commonContinuumOSCompiler route finiteGap =
  ymOSSameObject route (cutoffToContinuum route finiteGap)

-- Energy-form route: unlike the first parity draft, there is no separate
-- `formGapCompiler` hypothesis.  The finite vacuum-form-gap datum is constructed
-- directly by YMClayBoundedFormParityExact from the bounded physical form
-- package, matching the Lean FormHamiltonian consumer semantics.
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

-- Source/clustering route.  This remains abstract at this layer because the
-- live R387 specialization is supplied by YMClayFullChainParityExact below.
record SourceClusteringRoute
    (SpectralRepresentation CovarianceDecay FiniteGap : Set) : Set₁ where
  field
    spectralRepresentation : SpectralRepresentation
    covarianceDecay : CovarianceDecay
    clusteringGapCompiler :
      SpectralRepresentation → CovarianceDecay → FiniteGap

open SourceClusteringRoute public

finiteGapOfSourceClustering :
  ∀ {SpectralRepresentation CovarianceDecay FiniteGap} →
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
  ∀ {SpectralRepresentation CovarianceDecay FiniteGap ContinuumGap
      ContinuumHamiltonian Vacuum GapParameter} →
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
