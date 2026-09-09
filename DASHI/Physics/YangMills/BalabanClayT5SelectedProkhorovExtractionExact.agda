{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanClayT5SelectedProkhorovExtractionExact where

------------------------------------------------------------------------
-- SELECTED-CONVERGENCE PROKHOROV EXTRACTION
--
-- Same literal-subsequence discipline as the earlier compiler, but with only a
-- convergence relation.  No total limit choice on arbitrary measure sequences
-- is required.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayT5CompactUniqueFullSequenceExact as LegacySubsequence
import DASHI.Physics.YangMills.BalabanClayT5SelectedSequentialConvergenceExact as Selected
import DASHI.Physics.YangMills.BalabanClayT5SelectedCompactUniqueFullSequenceExact as CompactUnique

record SelectedSubsequenceTightnessData (Measure : Set) : Set₁ where
  field
    convergence : Selected.SequentialConvergence Measure
    sequence : Nat → Measure
    TightMeasureSequence : (Nat → Measure) → Set
    everyLiteralSubsequenceTight :
      (subsequence : LegacySubsequence.SubsequenceWitness sequence) →
      TightMeasureSequence (LegacySubsequence.values subsequence)

open SelectedSubsequenceTightnessData public

record SelectedProkhorovAuthority (Measure : Set) : Set₁ where
  field
    extractFurther :
      (dataSet : SelectedSubsequenceTightnessData Measure) →
      (subsequence : LegacySubsequence.SubsequenceWitness (sequence dataSet)) →
      TightMeasureSequence dataSet (LegacySubsequence.values subsequence) →
      LegacySubsequence.SubsequenceWitness (LegacySubsequence.values subsequence)

    clusterLimit :
      (dataSet : SelectedSubsequenceTightnessData Measure) →
      LegacySubsequence.SubsequenceWitness (sequence dataSet) → Measure

    extractedConverges :
      (dataSet : SelectedSubsequenceTightnessData Measure) →
      (subsequence : LegacySubsequence.SubsequenceWitness (sequence dataSet)) →
      let tight = everyLiteralSubsequenceTight dataSet subsequence
          further = extractFurther dataSet subsequence tight
      in Selected.Converges (convergence dataSet)
          (LegacySubsequence.values further)
          (clusterLimit dataSet subsequence)

open SelectedProkhorovAuthority public

selectedFurther :
  ∀ {Measure} →
  (authority : SelectedProkhorovAuthority Measure) →
  (dataSet : SelectedSubsequenceTightnessData Measure) →
  (subsequence : LegacySubsequence.SubsequenceWitness (sequence dataSet)) →
  LegacySubsequence.SubsequenceWitness (LegacySubsequence.values subsequence)
selectedFurther authority dataSet subsequence =
  extractFurther authority dataSet subsequence
    (everyLiteralSubsequenceTight dataSet subsequence)

record SelectedCompactUniqueBridgeInputs (Measure : Set) : Set₁ where
  field
    tightness : SelectedSubsequenceTightnessData Measure
    target : Measure
    prokhorov : SelectedProkhorovAuthority Measure
    everyExtractedClusterPointIsTarget :
      (subsequence : LegacySubsequence.SubsequenceWitness
        (sequence tightness)) →
      clusterLimit prokhorov tightness subsequence ≡ target

open SelectedCompactUniqueBridgeInputs public

compileSelectedCompactUniqueData :
  ∀ {Measure} →
  SelectedCompactUniqueBridgeInputs Measure →
  CompactUnique.SelectedCompactUniqueData Measure
compileSelectedCompactUniqueData inputs = record
  { convergence = convergence (tightness inputs)
  ; sequence = sequence (tightness inputs)
  ; target = target inputs
  ; extractFurther = selectedFurther (prokhorov inputs) (tightness inputs)
  ; clusterLimit = clusterLimit (prokhorov inputs) (tightness inputs)
  ; extractedSubsequenceConverges =
      extractedConverges (prokhorov inputs) (tightness inputs)
  ; uniqueClusterPoint = everyExtractedClusterPointIsTarget inputs
  }

selectedProkhorovExtractionCompilerLevel : ProofLevel
selectedProkhorovExtractionCompilerLevel = machineChecked

selectedProkhorovAuthorityLevel : ProofLevel
selectedProkhorovAuthorityLevel = standardImported
