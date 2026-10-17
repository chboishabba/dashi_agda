module DASHI.Reasoning.Ternary27A5SixFaceReorganisationReceiptExact where

------------------------------------------------------------------------
-- CROSS-KERNEL RECEIPT FOR THE DIRECT A5/S6 SIX-FACE REORGANISATION
--
-- Companion Lean source now acts on the absolute six hypervoxel face labels,
-- induces the natural action on the fifteen unordered pairs and the dual six,
-- and proves that this direct 6+15+6 action preserves Schlaefli adjacency and
-- intertwines the independently defined E6 A5 root reflections.
--
-- This Agda owner records that promotion surface without claiming a Lean
-- kernel result as an Agda theorem.  The source-native Monster normalizer
-- conjugation receipt remains separate.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

record A5SixFaceReorganisationReceipt : Set where
  constructor a5-six-face-reorganisation-receipt
  field
    absoluteFaceSixAction : Set
    inducedPairFifteenAction : Set
    inducedDualSixAction : Set
    schlafliRelationPreservation : Set
    a5MinusculeActionIntertwiner : Set
    generatedSixActionIsS6 : Set
open A5SixFaceReorganisationReceipt public

record A5SixFaceBoundary : Set where
  constructor a5-six-face-boundary
  field
    leanDirectFaceActionSourceWritten : Bool
    leanPair15ActionSourceWritten : Bool
    leanSchlafliPreservationSourceWritten : Bool
    leanA5MinusculeIntertwinerSourceWritten : Bool
    leanS6ClosureSourceWritten : Bool
    agdaIndependentKernelProducerPaidHere : Bool
    monsterNormalizerConjugationPaid : Bool
    fullE6RawTernaryActionPaid : Bool
    boundaryNote : String
open A5SixFaceBoundary public

canonicalA5SixFaceBoundary : A5SixFaceBoundary
canonicalA5SixFaceBoundary =
  a5-six-face-boundary
    true true true true true
    false false false
    "The direct six-face A5/S6 action is source-written by the companion Lean producer. Agda records the receipt surface only. The remaining scientific weld is source-native normalizer conjugation on the already-owned Face6/Axis6 translation and modulation generators; full E6 action is not inferred from the A5 stabilizer subgroup."
