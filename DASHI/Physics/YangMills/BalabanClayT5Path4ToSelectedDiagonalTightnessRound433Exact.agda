{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanClayT5Path4ToSelectedDiagonalTightnessRound433Exact where

------------------------------------------------------------------------
-- ROUND433 / PATH4 GAUGE ENERGY -> SELECTED DIAGONAL TIGHTNESS
--
-- This is the preferred H2a compiler.
--
-- The concrete Path4 gauge-fixed energy already supplies machine-checked
-- pointwise nonnegativity and coercivity once realized as the selected T5
-- observable.  The selected moment theorem supplies the cutoff-indexed moment
-- inequality.  Therefore the only physical containment content retained by
-- this route is:
--
--   * the selected expectation has the probability-integral/Markov semantics
--     needed to turn the moment bound into a sublevel complement bound;
--   * the chosen coercive sublevel is compact/admissible in the selected
--     measure topology;
--   * the Path4 observable is present/renormalized on the exact expectation
--     producer.
--
-- R433 compiles those inputs directly into R431 selected-diagonal tightness.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false)
open import Data.Rational using (ℚ)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanClayT5ThermodynamicUniformIntegrabilityExact as T5
import DASHI.Physics.YangMills.BalabanClayT5SelectedMomentCompactContainmentExact as SelectedMoment
import DASHI.Physics.YangMills.BalabanClayT5Path4GaugeEnergyObservableRealizationExact as Realization
import DASHI.Physics.YangMills.BalabanClayT5Path4GaugeEnergyMarkovBridgeExact as Path4
import DASHI.Physics.YangMills.BalabanClayT5MomentToSelectedDiagonalTightnessRound432Exact as R432
import DASHI.Physics.YangMills.BalabanClayT5SelectedDiagonalTightnessRound431Exact as R431

asSelectedMomentCompactContainment :
  ∀ {Measure Observable Configuration Epsilon Witness}
    {expectationData :
      T5.PhysicalExpectationProducerData Measure Observable ℚ}
    {realization :
      Realization.Path4GaugeEnergyObservableRealization
        Measure Observable Configuration expectationData} →
  Path4.Path4SelectedMomentContainmentInputs
    Measure Observable Configuration Epsilon Witness
    expectationData realization →
  SelectedMoment.SelectedMomentCompactContainmentInputs
    Measure Observable ℚ Epsilon Witness expectationData
asSelectedMomentCompactContainment
    {realization = realization} inputs = record
  { SelectedMoment.SelectedMomentCompactContainmentInputs.Admissible =
      Path4.Admissible inputs
  ; SelectedMoment.SelectedMomentCompactContainmentInputs.Controls =
      Path4.Controls inputs
  ; SelectedMoment.SelectedMomentCompactContainmentInputs.tightnessObservable =
      λ epsilon →
        Realization.path4GaugeEnergyObservable realization
  ; SelectedMoment.SelectedMomentCompactContainmentInputs.momentOrder =
      Path4.momentOrder inputs
  ; SelectedMoment.SelectedMomentCompactContainmentInputs.compactWitness =
      Path4.compactWitness inputs
  ; SelectedMoment.SelectedMomentCompactContainmentInputs.tightnessObservableRenormalized =
      λ epsilon →
        Realization.path4GaugeEnergyRenormalized (Path4.renormalized inputs)
  ; SelectedMoment.SelectedMomentCompactContainmentInputs.compactWitnessAdmissible =
      Path4.compactWitnessAdmissible inputs
  ; SelectedMoment.SelectedMomentCompactContainmentInputs.momentBoundControlsCompactComplement =
      λ epsilon cutoff bound →
        Path4.selectedExpectationMarkovSublevel inputs epsilon cutoff
          (Realization.path4GaugeEnergyObservablePointwiseNonnegative realization)
          (Realization.path4GaugeEnergyObservablePointwiseCoercive realization)
          bound
  }

path4ToSelectedDiagonalTightness :
  ∀ {Measure Observable Configuration Epsilon Witness}
    {expectationData :
      T5.PhysicalExpectationProducerData Measure Observable ℚ}
    {realization :
      Realization.Path4GaugeEnergyObservableRealization
        Measure Observable Configuration expectationData}
    (inputs :
      Path4.Path4SelectedMomentContainmentInputs
        Measure Observable Configuration Epsilon Witness
        expectationData realization) →
  R431.SelectedDiagonalTightnessInputs expectationData
path4ToSelectedDiagonalTightness inputs =
  R432.momentContainmentToSelectedDiagonalTightness
    (Path4.measureLimit inputs)
    (asSelectedMomentCompactContainment inputs)

round433Path4ToDiagonalTightnessCompilerLevel : ProofLevel
round433Path4ToDiagonalTightnessCompilerLevel = machineChecked

round433PointwiseNonnegativityLevel : ProofLevel
round433PointwiseNonnegativityLevel = machineChecked

round433PointwiseCoercivityLevel : ProofLevel
round433PointwiseCoercivityLevel = machineChecked

round433SelectedExpectationMarkovSemanticsLevel : ProofLevel
round433SelectedExpectationMarkovSemanticsLevel = conditional

round433Path4GaugeEnergyRenormalizationLevel : ProofLevel
round433Path4GaugeEnergyRenormalizationLevel = conditional

round433CompactCoerciveSublevelLevel : ProofLevel
round433CompactCoerciveSublevelLevel = conditional

round433IndependentTightnessTheoremRequired : Bool
round433IndependentTightnessTheoremRequired = false
