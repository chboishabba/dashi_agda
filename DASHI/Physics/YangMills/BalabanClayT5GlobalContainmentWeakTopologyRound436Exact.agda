{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanClayT5GlobalContainmentWeakTopologyRound436Exact where

------------------------------------------------------------------------
-- ROUND436 / GLOBAL H2a + SHARED WEAK TOPOLOGY -> R434 PACKAGE
--
-- This is the preferred compactness/uniqueness constructor.
--
-- Physical inputs:
--   (1) exact global selected moment compact containment;
--   (2) the same T5 bounded expectations define the selected weak measure
--       topology and determine measures.
--
-- Everything else is compiler/standard topology:
--   selected diagonal tightness,
--   subsequence tightness,
--   Prokhorov extraction,
--   cluster-point equality,
--   full selected measure convergence.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanClayT5LimitAndNontrivialityExact as Limit
import DASHI.Physics.YangMills.BalabanClayT5ThermodynamicUniformIntegrabilityExact as T5
import DASHI.Physics.YangMills.BalabanClayT5SelectedMomentCompactContainmentExact as Moment
import DASHI.Physics.YangMills.BalabanClayT5MomentToSelectedDiagonalTightnessRound432Exact as R432
import DASHI.Physics.YangMills.BalabanClayT5SelectedDiagonalTightnessRound431Exact as R431
import DASHI.Physics.YangMills.BalabanClayT5SubsequenceProkhorovExtractionExact as Prokhorov
import DASHI.Physics.YangMills.BalabanClayT5CompactUniqueFullSequenceExact as Compact
import DASHI.Physics.YangMills.BalabanClayT5SelectedWeakTopologyMeaningRound435Exact as R435
import DASHI.Physics.YangMills.BalabanClayT5GlobalContainmentCompactnessRound434Exact as R434

record GlobalContainmentWeakTopologyInputs
    {Measure Observable Scalar : Set}
    (expectationData :
      T5.PhysicalExpectationProducerData Measure Observable Scalar)
    (Epsilon Witness : Set) : Set₂ where
  field
    convergence : Limit.SequentialLimit Measure

    globalContainment :
      Moment.SelectedMomentCompactContainmentInputs
        Measure Observable Scalar Epsilon Witness expectationData

    prokhorovAuthority :
      Prokhorov.ProkhorovSubsequenceExtractionAuthority Measure

    weakTopologyMeaning :
      R435.SelectedT5WeakTopologyMeaning
        expectationData
        selectedPhysicalTightness

    compactUniqueFullConvergenceAuthority :
      Compact.CompactUniqueFullConvergenceAuthority Measure

  selectedTightness :
    R431.SelectedDiagonalTightnessInputs expectationData
  selectedTightness =
    R432.momentContainmentToSelectedDiagonalTightness
      convergence globalContainment

  selectedPhysicalTightness :
    Prokhorov.PhysicalSubsequenceTightnessData Measure
  selectedPhysicalTightness =
    R431.asPhysicalSubsequenceTightnessData selectedTightness

open GlobalContainmentWeakTopologyInputs public

asR434GlobalContainmentCompactness :
  ∀ {Measure Observable Scalar Epsilon Witness}
    {expectationData :
      T5.PhysicalExpectationProducerData Measure Observable Scalar} →
  GlobalContainmentWeakTopologyInputs expectationData Epsilon Witness →
  R434.GlobalContainmentCompactnessInputs
    expectationData Epsilon Witness
asR434GlobalContainmentCompactness inputs = record
  { R434.GlobalContainmentCompactnessInputs.convergence =
      convergence inputs
  ; R434.GlobalContainmentCompactnessInputs.globalContainment =
      globalContainment inputs
  ; R434.GlobalContainmentCompactnessInputs.prokhorovAuthority =
      prokhorovAuthority inputs
  ; R434.GlobalContainmentCompactnessInputs.determiningUniqueness =
      R435.asR430DeterminingExpectationAuthority
        (weakTopologyMeaning inputs)
  ; R434.GlobalContainmentCompactnessInputs.compactUniqueFullConvergenceAuthority =
      compactUniqueFullConvergenceAuthority inputs
  }

round436PreferredCompactnessCompilerLevel : ProofLevel
round436PreferredCompactnessCompilerLevel = machineChecked

round436GlobalMomentCompactContainmentLevel : ProofLevel
round436GlobalMomentCompactContainmentLevel = conditional

round436SelectedWeakTopologyMeaningLevel : ProofLevel
round436SelectedWeakTopologyMeaningLevel = conditional

round436ClusterPointEqualityLevel : ProofLevel
round436ClusterPointEqualityLevel = machineChecked

round436FullSelectedMeasureConvergenceLevel : ProofLevel
round436FullSelectedMeasureConvergenceLevel = machineChecked

round436IndependentUniquenessTheoremRequired : Bool
round436IndependentUniquenessTheoremRequired = false
