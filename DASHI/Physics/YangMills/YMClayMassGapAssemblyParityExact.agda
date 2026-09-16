{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YMClayMassGapAssemblyParityExact where

------------------------------------------------------------------------
-- AGDA PARITY FOR LEAN RequestProject.YangMills.Clay.MassGapAssembly
--
-- Lean now exposes two finite-gap producers (energy-form and source/clustering)
-- feeding one common cutoff->continuum->OS spine.  This Agda owner mirrors that
-- exact consumer topology and deliberately keeps the literal physical inputs
-- visible.  The theorem below is composition only: it does not manufacture a
-- Yang--Mills cutoff family, continuum graph limit, or YM/OS same-object weld.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.YMClayBoundedFormParityExact as Form

-- Final consumer shape.  The concrete proposition families are parameters so
-- the same theorem can be instantiated by the existing spectral/OS owners.
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

-- One common continuum/OS spine, matching Lean CutoffFamily + OSWeld.
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

-- Energy-form route.  The form package itself is concrete; the only bridge
-- here is the already-proved mathematical implication from its vacuum-null,
-- coercive form data to the finite gap object expected by the common spine.
record EnergyFormRoute
    (Hilbert Scalar FiniteGap : Set) : Set₁ where
  field
    finiteForms : Form.BoundedFormGapPackage Hilbert Scalar
    formGapCompiler : Form.BoundedFormGapPackage Hilbert Scalar → FiniteGap

open EnergyFormRoute public

finiteGapOfEnergyForms :
  ∀ {Hilbert Scalar FiniteGap} →
  EnergyFormRoute Hilbert Scalar FiniteGap → FiniteGap
finiteGapOfEnergyForms route = formGapCompiler route (finiteForms route)

-- Source/clustering route.  This mirrors Lean's
-- SpectralRepresentation + covariance decay -> finite vacuum gap theorem.
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
  ∀ {Hilbert Scalar FiniteGap ContinuumGap ContinuumHamiltonian Vacuum GapParameter} →
  EnergyFormRoute Hilbert Scalar FiniteGap →
  CommonContinuumOSRoute
    FiniteGap ContinuumGap ContinuumHamiltonian Vacuum GapParameter →
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

-- Validation sentinels name the existence of the two executable assemblers.
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
energyFormToFiniteGapMathematicsLevel = conditional

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
