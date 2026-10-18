{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanClayT5MomentToSelectedDiagonalTightnessRound432Exact where

------------------------------------------------------------------------
-- ROUND432 / TYPED MOMENT COMPACT CONTAINMENT -> R431 H2a TIGHTNESS
--
-- No new compactness theorem is introduced here.
--
-- BalabanClayT5SelectedMomentCompactContainmentExact already constructs one
-- UniformTightnessCertificate on the literal selected diagonal measure sequence
-- from:
--
--   * the existing cutoff-indexed moment inequality;
--   * one selected coercive observable/order;
--   * one compact witness per epsilon;
--   * the physical Markov/sublevel containment implication.
--
-- R432 installs exactly that certificate as R431's selected-diagonal tightness
-- object.  Hereditary subsequence tightness remains compiler-owned.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanClayT5LimitAndNontrivialityExact as Limit
import DASHI.Physics.YangMills.BalabanClayT5ThermodynamicUniformIntegrabilityExact as T5
import DASHI.Physics.YangMills.BalabanClayT5UniformTightnessSubsequenceInheritanceExact as Uniform
import DASHI.Physics.YangMills.BalabanClayT5SelectedMomentCompactContainmentExact as Moment
import DASHI.Physics.YangMills.BalabanClayT5SelectedDiagonalTightnessRound431Exact as R431

momentContainmentToSelectedDiagonalTightness :
  ∀ {Measure Observable Scalar Epsilon Witness}
    {expectationData :
      T5.PhysicalExpectationProducerData Measure Observable Scalar}
    (convergence : Limit.SequentialLimit Measure)
    (inputs :
      Moment.SelectedMomentCompactContainmentInputs
        Measure Observable Scalar Epsilon Witness expectationData) →
  R431.SelectedDiagonalTightnessInputs expectationData
momentContainmentToSelectedDiagonalTightness
    {Measure = Measure} {Epsilon = Epsilon} {Witness = Witness}
    convergence inputs = record
  { R431.SelectedDiagonalTightnessInputs.convergence =
      convergence
  ; R431.SelectedDiagonalTightnessInputs.TightMeasureSequence =
      Uniform.UniformTightnessCertificate
        Measure Epsilon Witness
        (Moment.Admissible inputs)
        (Moment.Controls inputs)
  ; R431.SelectedDiagonalTightnessInputs.selectedDiagonalTight =
      Moment.selectedDiagonalUniformTightnessCertificate inputs
  ; R431.SelectedDiagonalTightnessInputs.subsequenceAuthority = record
      { Uniform.TightnessSubsequenceAuthority.literalSubsequenceOfTightSequenceIsTight =
          λ sequence certificate subsequence →
            Uniform.restrictUniformTightnessToSubsequence
              certificate subsequence
      }
  }

round432MomentToDiagonalTightnessCompilerLevel : ProofLevel
round432MomentToDiagonalTightnessCompilerLevel = machineChecked

round432TypedMomentInequalityReuseLevel : ProofLevel
round432TypedMomentInequalityReuseLevel = machineChecked

round432PhysicalMomentCompactContainmentLevel : ProofLevel
round432PhysicalMomentCompactContainmentLevel = conditional

round432IndependentSelectedDiagonalTightnessTheoremRequired : Bool
round432IndependentSelectedDiagonalTightnessTheoremRequired = false
