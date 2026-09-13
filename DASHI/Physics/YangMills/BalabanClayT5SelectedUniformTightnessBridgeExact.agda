{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanClayT5SelectedUniformTightnessBridgeExact where

------------------------------------------------------------------------
-- UNIFORM TIGHTNESS -> SELECTED-CONVERGENCE PROKHOROV INPUT
--
-- Uniform compact containment is independent of any chosen total limit
-- operator.  This adapter retains the existing uniform-tightness certificate
-- and restricts it to literal subsequences while carrying only the selected
-- convergence relation needed by Prokhorov extraction.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayT5CompactUniqueFullSequenceExact as LegacySubsequence
import DASHI.Physics.YangMills.BalabanClayT5UniformTightnessSubsequenceInheritanceExact as Uniform
import DASHI.Physics.YangMills.BalabanClayT5SelectedSequentialConvergenceExact as Selected
import DASHI.Physics.YangMills.BalabanClayT5SelectedProkhorovExtractionExact as Prokhorov

record SelectedUniformTightnessInputs
    (Measure Epsilon Witness : Set) : Set₁ where
  field
    convergence : Selected.SequentialConvergence Measure
    sequence : Nat → Measure
    Admissible : Epsilon → Witness → Set
    Controls : Epsilon → Witness → Measure → Set
    uniformlyTight :
      Uniform.UniformTightnessCertificate
        Measure Epsilon Witness Admissible Controls sequence

open SelectedUniformTightnessInputs public

compileSelectedSubsequenceTightnessData :
  ∀ {Measure Epsilon Witness} →
  SelectedUniformTightnessInputs Measure Epsilon Witness →
  Prokhorov.SelectedSubsequenceTightnessData Measure
compileSelectedSubsequenceTightnessData inputs = record
  { convergence = convergence inputs
  ; sequence = sequence inputs
  ; TightMeasureSequence =
      Uniform.UniformTightnessCertificate
        _ _ _ (Admissible inputs) (Controls inputs)
  ; everyLiteralSubsequenceTight = λ subsequence →
      Uniform.restrictUniformTightnessToSubsequence
        (uniformlyTight inputs) subsequence
  }

selectedUniformTightnessBridgeLevel : ProofLevel
selectedUniformTightnessBridgeLevel = machineChecked
