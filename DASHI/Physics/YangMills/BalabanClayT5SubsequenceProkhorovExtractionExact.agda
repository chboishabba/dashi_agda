{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanClayT5SubsequenceProkhorovExtractionExact where

------------------------------------------------------------------------
-- T5 RELATIVE COMPACTNESS: LITERAL SUBSEQUENCE -> PROKHOROV EXTRACTION
--
-- The historical PhysicalMeasureCompactnessData stores one projective marginal
-- family and Set-valued Prokhorov/subsequence receipts.  That is useful
-- archaeology but is not typed strongly enough to prove that *every literal
-- subsequence of the selected diagonal physical measure sequence* has a
-- convergent further subsequence.
--
-- This module gives the least-privilege typed surface.  The physical input is
-- subsequence-indexed tightness of the literal selected sequence.  Standard
-- Prokhorov/sequential-compactness authority performs only the generic
-- extraction.  No unrelated measure family may satisfy the premise.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayT5LimitAndNontrivialityExact as Limit
import DASHI.Physics.YangMills.BalabanClayT5CompactUniqueFullSequenceExact as CompactUnique

record PhysicalSubsequenceTightnessData (Measure : Set) : Set₁ where
  field
    convergence : Limit.SequentialLimit Measure
    sequence : Nat → Measure

    -- Tightness is deliberately a predicate on the actual extracted measure
    -- sequence, not on a detached marginal ledger.
    TightMeasureSequence : (Nat → Measure) → Set

    -- This is the physical theorem: every literal subsequence of the selected
    -- diagonal sequence remains uniformly tight in the selected topology.
    everyLiteralSubsequenceTight :
      (subsequence : CompactUnique.SubsequenceWitness sequence) →
      TightMeasureSequence (CompactUnique.values subsequence)

open PhysicalSubsequenceTightnessData public

record ProkhorovSubsequenceExtractionAuthority (Measure : Set) : Set₁ where
  field
    extractConvergentFurtherSubsequence :
      (dataSet : PhysicalSubsequenceTightnessData Measure) →
      (subsequence : CompactUnique.SubsequenceWitness
        (sequence dataSet)) →
      TightMeasureSequence dataSet (CompactUnique.values subsequence) →
      CompactUnique.SubsequenceWitness (CompactUnique.values subsequence)

    extractedClusterLimit :
      (dataSet : PhysicalSubsequenceTightnessData Measure) →
      (subsequence : CompactUnique.SubsequenceWitness
        (sequence dataSet)) → Measure

    extractedFurtherConverges :
      (dataSet : PhysicalSubsequenceTightnessData Measure) →
      (subsequence : CompactUnique.SubsequenceWitness
        (sequence dataSet)) →
      let tight = everyLiteralSubsequenceTight dataSet subsequence
          further = extractConvergentFurtherSubsequence
            dataSet subsequence tight
      in Limit.Converges (convergence dataSet)
          (CompactUnique.values further)
          (extractedClusterLimit dataSet subsequence)

open ProkhorovSubsequenceExtractionAuthority public

extractPhysicalFurtherSubsequence :
  ∀ {Measure} →
  (authority : ProkhorovSubsequenceExtractionAuthority Measure) →
  (dataSet : PhysicalSubsequenceTightnessData Measure) →
  (subsequence : CompactUnique.SubsequenceWitness (sequence dataSet)) →
  CompactUnique.SubsequenceWitness (CompactUnique.values subsequence)
extractPhysicalFurtherSubsequence authority dataSet subsequence =
  extractConvergentFurtherSubsequence authority dataSet subsequence
    (everyLiteralSubsequenceTight dataSet subsequence)

physicalFurtherSubsequenceConverges :
  ∀ {Measure} →
  (authority : ProkhorovSubsequenceExtractionAuthority Measure) →
  (dataSet : PhysicalSubsequenceTightnessData Measure) →
  (subsequence : CompactUnique.SubsequenceWitness (sequence dataSet)) →
  Limit.Converges (convergence dataSet)
    (CompactUnique.values
      (extractPhysicalFurtherSubsequence authority dataSet subsequence))
    (extractedClusterLimit authority dataSet subsequence)
physicalFurtherSubsequenceConverges authority dataSet subsequence =
  extractedFurtherConverges authority dataSet subsequence

------------------------------------------------------------------------
-- Adapter into Round194 relative sequential compactness.
-- Cluster-point uniqueness remains an intentionally separate physical theorem.
------------------------------------------------------------------------

record PhysicalCompactUniqueBridgeInputs (Measure : Set) : Set₁ where
  field
    tightness : PhysicalSubsequenceTightnessData Measure
    target : Measure
    prokhorovAuthority : ProkhorovSubsequenceExtractionAuthority Measure

    -- The second physical theorem: every cluster point produced from every
    -- literal subsequence is exactly the selected continuum target.
    everyExtractedClusterPointIsTarget :
      (subsequence : CompactUnique.SubsequenceWitness
        (sequence tightness)) →
      extractedClusterLimit prokhorovAuthority tightness subsequence ≡ target

open PhysicalCompactUniqueBridgeInputs public

compileSequentialCompactUniqueData :
  ∀ {Measure} →
  PhysicalCompactUniqueBridgeInputs Measure →
  CompactUnique.SequentialCompactUniqueData Measure
compileSequentialCompactUniqueData inputs = record
  { convergence = convergence (tightness inputs)
  ; sequence = sequence (tightness inputs)
  ; target = target inputs
  ; extractFurther =
      extractPhysicalFurtherSubsequence
        (prokhorovAuthority inputs) (tightness inputs)
  ; clusterLimit =
      extractedClusterLimit (prokhorovAuthority inputs) (tightness inputs)
  ; extractedSubsequenceConverges =
      physicalFurtherSubsequenceConverges
        (prokhorovAuthority inputs) (tightness inputs)
  ; uniqueClusterPoint = everyExtractedClusterPointIsTarget inputs
  }

subsequenceProkhorovExtractionCompilerLevel : ProofLevel
subsequenceProkhorovExtractionCompilerLevel = machineChecked

prokhorovSubsequenceExtractionAuthorityLevel : ProofLevel
prokhorovSubsequenceExtractionAuthorityLevel = standardImported

physicalEveryLiteralSubsequenceTightLevel : ProofLevel
physicalEveryLiteralSubsequenceTightLevel = conditional

physicalEveryExtractedClusterPointIsTargetLevel : ProofLevel
physicalEveryExtractedClusterPointIsTargetLevel = conditional
