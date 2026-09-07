{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanClayCurrentTerminalCutsetRound195Exact where

------------------------------------------------------------------------
-- ROUND195: REFINE T1 BY WRONGTYPE-SAFE PROKHOROV EXTRACTION
--
-- Round194 identified relative sequential compactness of the literal selected
-- diagonal measure sequence as a physical leaf.  The historical compactness
-- record is insufficient for that theorem because its projective marginal
-- family is not subsequence-indexed and its Prokhorov conclusion is Set-valued.
--
-- Round195 therefore replaces the broad T1 leaf by the exact physical premise
-- consumed by standard Prokhorov extraction: every literal subsequence of the
-- selected diagonal sequence is tight in the selected measure topology.
------------------------------------------------------------------------

open import Agda.Builtin.List using (List; _∷_; [])
open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayCurrentTerminalCutsetRound194Exact as R194
import DASHI.Physics.YangMills.BalabanClayT5SubsequenceProkhorovExtractionExact as Prokhorov
import DASHI.Physics.YangMills.YMOperatorDomainContinuumFrontier2026Exact as Frontier

data T5PreferredContinuumLeaf195 : Set where
  physicalEveryLiteralSubsequenceTight : T5PreferredContinuumLeaf195
  physicalEveryExtractedClusterPointIsTarget : T5PreferredContinuumLeaf195
  physicalMeasurePropertySequentialClosure : T5PreferredContinuumLeaf195
  physicalGramReflectionMeasureTopologyClosure : T5PreferredContinuumLeaf195
  physicalContinuumSchwingerAxioms : T5PreferredContinuumLeaf195

preferredT5ContinuumCut195 : List T5PreferredContinuumLeaf195
preferredT5ContinuumCut195 =
  physicalEveryLiteralSubsequenceTight ∷
  physicalEveryExtractedClusterPointIsTarget ∷
  physicalMeasurePropertySequentialClosure ∷
  physicalGramReflectionMeasureTopologyClosure ∷
  physicalContinuumSchwingerAxioms ∷ []

-- Generic Prokhorov extraction and compact+unique -> full convergence are not
-- physical search leaves on this route.
prokhorovExtractionAuthorityLevel : ProofLevel
prokhorovExtractionAuthorityLevel =
  Prokhorov.prokhorovSubsequenceExtractionAuthorityLevel

subsequenceExtractionCompilerLevel : ProofLevel
subsequenceExtractionCompilerLevel =
  Prokhorov.subsequenceProkhorovExtractionCompilerLevel

physicalSubsequenceTightnessProducerLevel : ProofLevel
physicalSubsequenceTightnessProducerLevel =
  Prokhorov.physicalEveryLiteralSubsequenceTightLevel

physicalClusterPointUniquenessProducerLevel : ProofLevel
physicalClusterPointUniquenessProducerLevel =
  Prokhorov.physicalEveryExtractedClusterPointIsTargetLevel

-- Proof-search first-missing cut: historical Prokhorov/subsequence Set receipts
-- are evidence coordinates, not inhabitants of the literal subsequence theorem.
data T1PrerequisiteStatus : Set where
  missingLiteralSubsequenceTightness : T1PrerequisiteStatus
  readyForStandardProkhorovExtraction : T1PrerequisiteStatus

preferredCurrentT1Status : T1PrerequisiteStatus
preferredCurrentT1Status = missingLiteralSubsequenceTightness

round194CutRetainedForCompatibility : ProofLevel
round194CutRetainedForCompatibility =
  R194.currentYMTerminalCutsetRound194Level

finiteToContinuumYMStillOpen :
  Frontier.finiteToContinuumYMConstructionClosed
    Frontier.canonicalYMOperatorContinuumFrontier ≡ false
finiteToContinuumYMStillOpen = refl

continuumOSWightmanStillOpen :
  Frontier.continuumOSWightmanPackageClosed
    Frontier.canonicalYMOperatorContinuumFrontier ≡ false
continuumOSWightmanStillOpen = refl

currentYMTerminalCutsetRound195Level : ProofLevel
currentYMTerminalCutsetRound195Level = machineChecked

literalPreferredT5ContinuumLeaf195Level : ProofLevel
literalPreferredT5ContinuumLeaf195Level = conditional
