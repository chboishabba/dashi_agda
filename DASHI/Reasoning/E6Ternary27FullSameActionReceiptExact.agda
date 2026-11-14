module DASHI.Reasoning.E6Ternary27FullSameActionReceiptExact where

------------------------------------------------------------------------
-- CROSS-KERNEL RECEIPT: FULL E6 MATRIX <-> TERNARY-27 SAME ACTION
--
-- Companion Lean #47 now source-writes three finite producers beyond the
-- earlier A5/S6 receipt:
--
--   1. synchronized closure of the selected Q2 matrix stabilizer with the
--      direct six-face S6 action, including an explicit old-seed -> alpha0
--      transporter and conjugacy;
--   2. synchronized closure of the complete 51,840-element E6 mod-3 matrix
--      image with the 51,840-element faithful permutation image on the same
--      raw ternary 27;
--   3. Coxeter-coherent action on the gauge-free 72-root-chart x 27-state
--      atlas, rather than an artificial unique transition between chart pairs.
--
-- This Agda owner keeps kernel authority separate.  It records the exact
-- theorem-facing receipt surface and marks the source-native Monster/3B
-- normalizer realization and Albert/Jordan algebra as separate obligations.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

record SelectedStabilizerSameObjectReceipt : Set where
  constructor selected-stabilizer-same-object-receipt
  field
    selectedQ2MatrixStabilizer : Set
    alpha0MatrixStabilizer : Set
    faceS6Action : Set
    seedConjugacy : Set
    synchronizedMatrixFaceGraph : Set
    uniqueMatrixToFaceAction : Set
    uniqueFaceActionToMatrix : Set
open SelectedStabilizerSameObjectReceipt public

record FullE6TernarySameActionReceipt : Set where
  constructor full-e6-ternary-same-action-receipt
  field
    generatedMatrixImage : Set
    generatedTernary27PermutationImage : Set
    synchronizedFullActionGraph : Set
    matrixProjectionExact : Set
    ternaryPermutationProjectionFaithful : Set
    sixGeneratorLabelIntertwiner : Set
    coxeterInvolutions : Set
    coxeterAdjacentBraid : Set
    coxeterNonadjacentCommutation : Set
open FullE6TernarySameActionReceipt public

record SeventyTwoChartAtlasReceipt : Set where
  constructor seventy-two-chart-atlas-receipt
  field
    rootChartCarrier72 : Set
    ternaryFibre27 : Set
    simultaneousGeneratorAction : Set
    schlafliTransport : Set
    gaugeFreeActionGroupoidCoherence : Set
open SeventyTwoChartAtlasReceipt public

record FullSameActionBoundary : Set where
  constructor full-same-action-boundary
  field
    leanSelectedMatrixFaceSameObjectSourceWritten : Bool
    leanOldSeedConjugacySourceWritten : Bool
    leanFull51840MatrixPermutationSyncSourceWritten : Bool
    leanTernaryCoxeterPresentationSourceWritten : Bool
    leanSeventyTwoByTwentySevenAtlasSourceWritten : Bool
    leanGaugeFreeAtlasCoherenceSourceWritten : Bool
    agdaIndependentFiniteProducerPaidHere : Bool
    fullFiniteE6RawTernaryAtlasSourceWritten : Bool
    monsterNormalizerPhysicalRealizationPaid : Bool
    albertJordanStructurePaid : Bool
    fullTernary240E8RecognitionPaid : Bool
    boundaryNote : String
open FullSameActionBoundary public

canonicalFullSameActionBoundary : FullSameActionBoundary
canonicalFullSameActionBoundary =
  full-same-action-boundary
    true true true true true true
    false true false false false
    "The companion Lean branch now closes the finite E6 same-action problem through an explicit selected-stabilizer conjugacy, a bijective 51,840 matrix/permutation synchronized closure, the E6 Coxeter relations on the raw ternary 27, and a gauge-free 72-chart x 27 action. Agda records these as cross-kernel receipts only. Remaining stronger obligations are source-native Monster/3B normalizer realization, Albert/Jordan algebra, and any full ternary-240 <-> literal-E8 recognition."
