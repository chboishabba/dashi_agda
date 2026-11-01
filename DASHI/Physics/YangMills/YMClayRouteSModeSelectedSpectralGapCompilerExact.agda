{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YMClayRouteSModeSelectedSpectralGapCompilerExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base as ℚ using (ℚ)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram
import DASHI.Physics.YangMills.BalabanConnectedCovarianceExpectationLimitRound278Exact as R278
import DASHI.Physics.YangMills.BalabanT5UnlocalizedJSourceLocalizationRound318Exact as R318
import DASHI.Physics.YangMills.BalabanQuantitativePositiveTimeCyclicityRound299Exact as R299
import DASHI.Physics.YangMills.BalabanCyclicSubgapNonzeroByConstructionRound297Exact as R297
import DASHI.Physics.YangMills.BalabanPositiveSpectralComponentLowerRound300Exact as R300
import DASHI.Physics.YangMills.BalabanQuantitativeSubgapSpectralCoreRound301Exact as R301
import DASHI.Physics.YangMills.BalabanSubgapGeometricSeparationRound293Exact as R293
import DASHI.Physics.YangMills.BalabanClayT5ClusteringToTransferGapExact as Gap
import DASHI.Physics.YangMills.YMClayRouteSH1ModeSelectedContinuumUpperExact as Source

------------------------------------------------------------------------
-- ROUTE-S MODE-SELECTED SPECTRAL CONTRADICTION
--
-- The preferred source compiler now produces the exact continuum half-rate
-- upper directly.  R300 already compiles a SAME-Hamiltonian positive spectral
-- component decomposition to its lower correlation bound; R301 consumes only
-- that lower bound, the physical energy->decay ordering, and standard rational
-- geometric domination.
--
-- Hence the clean terminal contradiction factors as:
--
--   H1 + distance=time + selected limit closure
--       -> C_mode(t) <= (1/4)(1/2)^t
--
--   SAME-H spectral decomposition + energy/ratio semantics
--       -> positive alleged subgap component decays more slowly
--
--   standard geometric domination
--       -> contradiction.
--
-- This module does not identify the spectral energy with H_OS.  That remains
-- the H3 same-Hamiltonian / transfer-coordinate application theorem.
------------------------------------------------------------------------

record RouteSModeSelectedSpectralInputs
    {Measure TestObservable Energy Vector : Set}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    (base : R318.UnlocalizedT5StateFamilyJPresentation dataSet extension)
    (tests : R278.SelectedConnectedCovarianceTests dataSet)
    (quantitative : R299.QuantitativePositiveTimeVacuumCyclicity
      TestObservable Vector)
    (family : R297.ActualNonzeroSubgapFamily
      (R299.asPositiveTimeVacuumCyclicity quantitative))
    (decomposition : R300.PositiveSpectralComponentDecomposition
      dataSet extension tests quantitative family)
    : Set₁ where
  field
    source :
      Source.RouteSH1ModeSelectedInputs
        base tests quantitative family decomposition

    rates :
      R301.ModeIndexedSubgapRateSemantics
        dataSet extension tests quantitative family decomposition

    geometricDominance : R293.RationalGeometricDominance

open RouteSModeSelectedSpectralInputs public

routeSModeSelectedNoPositiveSubgap :
  ∀ {Measure TestObservable Energy Vector}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    {base : R318.UnlocalizedT5StateFamilyJPresentation dataSet extension}
    {tests : R278.SelectedConnectedCovarianceTests dataSet}
    {quantitative : R299.QuantitativePositiveTimeVacuumCyclicity
      TestObservable Vector}
    {family : R297.ActualNonzeroSubgapFamily
      (R299.asPositiveTimeVacuumCyclicity quantitative)}
    {decomposition : R300.PositiveSpectralComponentDecomposition
      dataSet extension tests quantitative family} →
  (inputs : RouteSModeSelectedSpectralInputs
    base tests quantitative family decomposition) →
  ∀ energy (mode : R297.SubgapMode family energy) →
  R301.PositiveEnergy (rates inputs) energy →
  R301.StrictlyBelow (rates inputs) energy
    (R301.gapCandidate (rates inputs)) →
  Gap.Empty
routeSModeSelectedNoPositiveSubgap
    {decomposition = decomposition} inputs =
  R301.noPositiveSubgapModeFromPositiveComponent
    (geometricDominance inputs)
    (rates inputs)
    (Source.h1ModeSelectedInputsBuildContinuumHalfRateUpper
      (source inputs))

------------------------------------------------------------------------
-- Pareto classification.
------------------------------------------------------------------------

arbitraryObservableSpectralEnvelopeRequired : Bool
arbitraryObservableSpectralEnvelopeRequired = false

arbitraryObservableSpectralEnvelopeRequiredIsFalse :
  arbitraryObservableSpectralEnvelopeRequired ≡ false
arbitraryObservableSpectralEnvelopeRequiredIsFalse = refl

separatePositiveOverlapLeafRequired : Bool
separatePositiveOverlapLeafRequired = false

separatePositiveOverlapLeafRequiredIsFalse :
  separatePositiveOverlapLeafRequired ≡ false
separatePositiveOverlapLeafRequiredIsFalse = refl

separateSpectralLowerInequalityLeafRequired : Bool
separateSpectralLowerInequalityLeafRequired = false

separateSpectralLowerInequalityLeafRequiredIsFalse :
  separateSpectralLowerInequalityLeafRequired ≡ false
separateSpectralLowerInequalityLeafRequiredIsFalse = refl

sameHamiltonianSpectralDecompositionStillPhysical : Bool
sameHamiltonianSpectralDecompositionStillPhysical = true

sameHamiltonianSpectralDecompositionStillPhysicalIsTrue :
  sameHamiltonianSpectralDecompositionStillPhysical ≡ true
sameHamiltonianSpectralDecompositionStillPhysicalIsTrue = refl

energyToDecayOrderingStillPhysical : Bool
energyToDecayOrderingStillPhysical = true

energyToDecayOrderingStillPhysicalIsTrue :
  energyToDecayOrderingStillPhysical ≡ true
energyToDecayOrderingStillPhysicalIsTrue = refl

modeSelectedSpectralContradictionCompilerLevel : ProofLevel
modeSelectedSpectralContradictionCompilerLevel = machineChecked

sameHamiltonianSpectralDecompositionLevel : ProofLevel
sameHamiltonianSpectralDecompositionLevel =
  R300.round300SameHamiltonianPositiveSpectralDecompositionLevel

energyToDecayOrderingLevel : ProofLevel
energyToDecayOrderingLevel =
  R301.round301PhysicalEnergyToDecayOrderingLevel

clayPromotion : Bool
clayPromotion = false

clayPromotionIsFalse : clayPromotion ≡ false
clayPromotionIsFalse = refl
