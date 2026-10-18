{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanClayT5SelectedDiagonalTightnessRound431Exact where

------------------------------------------------------------------------
-- ROUND431 / SELECTED DIAGONAL TIGHTNESS -> EVERY SUBSEQUENCE TIGHT
--
-- Relative compactness should not ask the Yang--Mills source theorem to prove
-- tightness again for every literal subsequence.  Once the selected diagonal
-- physical measure sequence is tight in the chosen topology, every literal
-- subsequence is tight by the standard hereditary property of tightness.
--
-- Thus the physical H2a theorem is reduced to ONE statement:
--
--   TightMeasureSequence (T5.diagonalMeasure expectationData).
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Nat using (Nat)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanClayT5LimitAndNontrivialityExact as Limit
import DASHI.Physics.YangMills.BalabanClayT5ThermodynamicUniformIntegrabilityExact as T5
import DASHI.Physics.YangMills.BalabanClayT5CompactUniqueFullSequenceExact as Compact
import DASHI.Physics.YangMills.BalabanClayT5SubsequenceProkhorovExtractionExact as Prokhorov

record TightnessSubsequenceAuthority
    (Measure : Set)
    (TightMeasureSequence : (Nat → Measure) → Set) : Set₁ where
  field
    literalSubsequenceOfTightSequenceIsTight :
      ∀ (sequence : Nat → Measure) →
      TightMeasureSequence sequence →
      (subsequence : Compact.SubsequenceWitness sequence) →
      TightMeasureSequence (Compact.values subsequence)

open TightnessSubsequenceAuthority public

record SelectedDiagonalTightnessInputs
    {Measure Observable Scalar : Set}
    (expectationData :
      T5.PhysicalExpectationProducerData Measure Observable Scalar) : Set₂ where
  field
    convergence : Limit.SequentialLimit Measure
    TightMeasureSequence : (Nat → Measure) → Set

    selectedDiagonalTight :
      TightMeasureSequence (T5.diagonalMeasure expectationData)

    subsequenceAuthority :
      TightnessSubsequenceAuthority Measure TightMeasureSequence

open SelectedDiagonalTightnessInputs public

everyLiteralDiagonalSubsequenceTight :
  ∀ {Measure Observable Scalar}
    {expectationData :
      T5.PhysicalExpectationProducerData Measure Observable Scalar}
    (inputs : SelectedDiagonalTightnessInputs expectationData)
    (subsequence :
      Compact.SubsequenceWitness (T5.diagonalMeasure expectationData)) →
  TightMeasureSequence inputs (Compact.values subsequence)
everyLiteralDiagonalSubsequenceTight
    {expectationData = expectationData} inputs subsequence =
  literalSubsequenceOfTightSequenceIsTight
    (subsequenceAuthority inputs)
    (T5.diagonalMeasure expectationData)
    (selectedDiagonalTight inputs)
    subsequence

asPhysicalSubsequenceTightnessData :
  ∀ {Measure Observable Scalar}
    {expectationData :
      T5.PhysicalExpectationProducerData Measure Observable Scalar} →
  SelectedDiagonalTightnessInputs expectationData →
  Prokhorov.PhysicalSubsequenceTightnessData Measure
asPhysicalSubsequenceTightnessData
    {expectationData = expectationData} inputs = record
  { Prokhorov.PhysicalSubsequenceTightnessData.convergence =
      convergence inputs
  ; Prokhorov.PhysicalSubsequenceTightnessData.sequence =
      T5.diagonalMeasure expectationData
  ; Prokhorov.PhysicalSubsequenceTightnessData.TightMeasureSequence =
      TightMeasureSequence inputs
  ; Prokhorov.PhysicalSubsequenceTightnessData.everyLiteralSubsequenceTight =
      everyLiteralDiagonalSubsequenceTight inputs
  }

round431SubsequenceTightnessCompilerLevel : ProofLevel
round431SubsequenceTightnessCompilerLevel = machineChecked

round431TightnessHereditaryAuthorityLevel : ProofLevel
round431TightnessHereditaryAuthorityLevel = standardImported

round431SelectedDiagonalTightnessLevel : ProofLevel
round431SelectedDiagonalTightnessLevel = conditional

round431IndependentEverySubsequenceTightInputRequired : Bool
round431IndependentEverySubsequenceTightInputRequired = false
