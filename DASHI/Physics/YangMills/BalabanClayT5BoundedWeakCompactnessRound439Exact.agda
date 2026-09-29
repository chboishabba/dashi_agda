{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanClayT5BoundedWeakCompactnessRound439Exact where

------------------------------------------------------------------------
-- ROUND439 / GLOBAL CONTAINMENT + R438 WEAK TOPOLOGY -> FULL CONVERGENCE
--
-- Preferred H2a/H2b chain with NO total SequentialLimit:
--
--   selected global moment compact containment
--     -> one uniform tightness certificate
--     -> every literal subsequence tight
--     -> Prokhorov extraction in the bounded-expectation weak topology
--     -> R438 cluster-point equality from P2 + determining bounded tests
--     -> compact+unique full selected-sequence convergence.
--
-- The only physical inputs are therefore:
--   * global compact containment on the literal selected family;
--   * bounded selected expectations determine the physical measure.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanClayT5ThermodynamicUniformIntegrabilityExact as T5
import DASHI.Physics.YangMills.BalabanClayT5SelectedMomentCompactContainmentExact as Moment
import DASHI.Physics.YangMills.BalabanClayT5UniformTightnessSubsequenceInheritanceExact as Uniform
import DASHI.Physics.YangMills.BalabanClayT5SelectedProkhorovExtractionExact as Prokhorov
import DASHI.Physics.YangMills.BalabanClayT5SelectedCompactUniqueFullSequenceExact as Compact
import DASHI.Physics.YangMills.BalabanClayT5BoundedExpectationWeakTopologyRound438Exact as R438

record BoundedWeakCompactnessInputs
    {Measure Observable Scalar : Set}
    (expectationData :
      T5.PhysicalExpectationProducerData Measure Observable Scalar)
    (Epsilon Witness : Set) : Set₂ where
  field
    globalContainment :
      Moment.SelectedMomentCompactContainmentInputs
        Measure Observable Scalar Epsilon Witness expectationData

    weakTopologyAuthority :
      R438.BoundedExpectationWeakTopologyAuthority expectationData

    prokhorovAuthority :
      Prokhorov.SelectedProkhorovAuthority Measure

    compactUniqueAuthority :
      Compact.SelectedCompactUniqueFullConvergenceAuthority Measure

open BoundedWeakCompactnessInputs public

selectedBoundedWeakTightness :
  ∀ {Measure Observable Scalar Epsilon Witness}
    {expectationData :
      T5.PhysicalExpectationProducerData Measure Observable Scalar} →
  BoundedWeakCompactnessInputs expectationData Epsilon Witness →
  R438.BoundedWeakSelectedTightness expectationData
selectedBoundedWeakTightness
    {Measure = Measure} {Epsilon = Epsilon} {Witness = Witness}
    inputs = record
  { R438.BoundedWeakSelectedTightness.TightMeasureSequence =
      Uniform.UniformTightnessCertificate
        Measure Epsilon Witness
        (Moment.Admissible (globalContainment inputs))
        (Moment.Controls (globalContainment inputs))
  ; R438.BoundedWeakSelectedTightness.everyLiteralDiagonalSubsequenceTight =
      λ subsequence →
        Uniform.restrictUniformTightnessToSubsequence
          (Moment.selectedDiagonalUniformTightnessCertificate
            (globalContainment inputs))
          subsequence
  }

selectedCompactUniqueBridgeInputs :
  ∀ {Measure Observable Scalar Epsilon Witness}
    {expectationData :
      T5.PhysicalExpectationProducerData Measure Observable Scalar} →
  (inputs :
    BoundedWeakCompactnessInputs expectationData Epsilon Witness) →
  Prokhorov.SelectedCompactUniqueBridgeInputs Measure
selectedCompactUniqueBridgeInputs
    {expectationData = expectationData} inputs = record
  { Prokhorov.SelectedCompactUniqueBridgeInputs.tightness =
      R438.asSelectedSubsequenceTightnessData
        (selectedBoundedWeakTightness inputs)
  ; Prokhorov.SelectedCompactUniqueBridgeInputs.target =
      T5.continuumMeasure (T5.thermodynamic expectationData)
  ; Prokhorov.SelectedCompactUniqueBridgeInputs.prokhorov =
      prokhorovAuthority inputs
  ; Prokhorov.SelectedCompactUniqueBridgeInputs.everyExtractedClusterPointIsTarget =
      R438.extractedClusterPointIsSelectedContinuum
        (weakTopologyAuthority inputs)
        (selectedBoundedWeakTightness inputs)
        (prokhorovAuthority inputs)
  }

selectedCompactUniqueData :
  ∀ {Measure Observable Scalar Epsilon Witness}
    {expectationData :
      T5.PhysicalExpectationProducerData Measure Observable Scalar} →
  BoundedWeakCompactnessInputs expectationData Epsilon Witness →
  Compact.SelectedCompactUniqueData Measure
selectedCompactUniqueData inputs =
  Prokhorov.compileSelectedCompactUniqueData
    (selectedCompactUniqueBridgeInputs inputs)

literalDiagonalConvergesToSelectedContinuum :
  ∀ {Measure Observable Scalar Epsilon Witness}
    {expectationData :
      T5.PhysicalExpectationProducerData Measure Observable Scalar}
    (inputs :
      BoundedWeakCompactnessInputs expectationData Epsilon Witness) →
  R438.BoundedExpectationConverges
    expectationData
    (T5.diagonalMeasure expectationData)
    (T5.continuumMeasure (T5.thermodynamic expectationData))
literalDiagonalConvergesToSelectedContinuum inputs =
  Compact.selectedFullSequenceConverges
    (compactUniqueAuthority inputs)
    (selectedCompactUniqueData inputs)

round439SelectedCompactnessCompilerLevel : ProofLevel
round439SelectedCompactnessCompilerLevel = machineChecked

round439GlobalMomentCompactContainmentLevel : ProofLevel
round439GlobalMomentCompactContainmentLevel = conditional

round439BoundedDeterminingClassMeaningLevel : ProofLevel
round439BoundedDeterminingClassMeaningLevel = conditional

round439ProkhorovAuthorityLevel : ProofLevel
round439ProkhorovAuthorityLevel = standardImported

round439CompactUniqueAuthorityLevel : ProofLevel
round439CompactUniqueAuthorityLevel = standardImported

round439FullSelectedMeasureConvergenceLevel : ProofLevel
round439FullSelectedMeasureConvergenceLevel = machineChecked

round439LegacyTotalSequentialLimitRequired : Bool
round439LegacyTotalSequentialLimitRequired = false

round439IndependentClusterUniquenessTheoremRequired : Bool
round439IndependentClusterUniquenessTheoremRequired = false
