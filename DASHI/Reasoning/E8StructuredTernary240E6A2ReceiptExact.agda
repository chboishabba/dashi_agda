module DASHI.Reasoning.E8StructuredTernary240E6A2ReceiptExact where

------------------------------------------------------------------------
-- CROSS-KERNEL RECEIPT: STRUCTURED TERNARY 240 THROUGH E6 x A2
--
-- The old count-matched F3^5 partition 72+81+81+6 is action-obstructed.
-- Companion Lean #47 now source-writes the correct replacement carrier
--
--   Q2_72 + A2Root_6 + (A2WeightTag_6 x Ternary27Point),
--
-- of total size 240.
--
-- E6 acts on Q2 and the ternary-27 fibre; A2 acts on its root/weight tags.
-- Those actions commute and satisfy their Coxeter relations.  Finite uniqueness
-- checks identify every mixed tagged state with exactly one literal E8 mixed
-- root by the pair (A2 weight, E6 Dynkin label), and every A2 tag with exactly
-- one literal A2 root.  The 72-sector consumes the earlier Q2/literal-E6
-- same-object equivalence.
--
-- The remaining full-E8 datum is a cross-branch Weyl generator outside the
-- W(E6) x W(A2) subgroup.  The old affine 81+81 route is not reopened.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

record StructuredTernary240Receipt : Set where
  constructor structured-ternary240-receipt
  field
    e6Root72Carrier : Set
    a2Root6Carrier : Set
    mixedWeightTag6 : Set
    ternary27Fibre : Set
    e6Action : Set
    a2Action : Set
    commutingActionReceipt : Set
    e6CoxeterReceipt : Set
    a2CoxeterReceipt : Set
    mixedLiteralUniquenessReceipt : Set
    a2LiteralUniquenessReceipt : Set
open StructuredTernary240Receipt public

record StructuredTernary240Boundary : Set where
  constructor structured-ternary240-boundary
  field
    oldAffine7281816ActionObstructionRetained : Bool
    leanStructured240CarrierSourceWritten : Bool
    leanE6ActionSourceWritten : Bool
    leanA2ActionSourceWritten : Bool
    leanE6A2CommutationSourceWritten : Bool
    leanMixedLiteralSameObjectSourceWritten : Bool
    leanA2LiteralSameObjectSourceWritten : Bool
    previousE6Root72SameObjectConsumed : Bool
    e6TimesA2BranchingSameObjectSourceWritten : Bool
    crossBranchWeylGeneratorPaid : Bool
    fullWE8StructuredTernaryActionPaid : Bool
    originalT5RelativeComplementSameObjectPaid : Bool
    agdaIndependentFiniteProducerPaidHere : Bool
    boundaryNote : String
open StructuredTernary240Boundary public

canonicalStructuredTernary240Boundary : StructuredTernary240Boundary
canonicalStructuredTernary240Boundary =
  structured-ternary240-boundary
    true true true true true true true true true
    false false false false
    "The correct structured 240 now reaches the exact W(E6) x W(A2) branching boundary. The older 72+81+81+6 F3^5 count partition remains formally action-obstructed. The next mathematical datum is one independently sourced cross-branch E8 Weyl generator (and its relations), not another cardinality partition. This Agda file records the companion Lean finite producer only; it does not claim an Agda kernel proof."
