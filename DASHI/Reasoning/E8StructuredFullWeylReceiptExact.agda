module DASHI.Reasoning.E8StructuredFullWeylReceiptExact where

------------------------------------------------------------------------
-- CROSS-KERNEL RECEIPT: STRUCTURED 240 -> INTRINSIC E8 WEYL ROOT DATUM
--
-- Companion Lean source now goes beyond the earlier W(E6) x W(A2) branching:
-- it reconstructs the E6+A2 bilinear form from inverse Cartan data, selects the
-- mixed `omega5 ; (0,-1)` state as a norm-two glue root, and defines the
-- cross-branch reflection from that pairing rather than by transporting the
-- literal E8 action.
--
-- The six E6 simple roots, the signed glue root and signed A2-b root give an
-- eight-root E8 Cartan Gram matrix with determinant one.  The reflection
-- relation is total/unique on all 240 structured roots and satisfies the E8
-- involution/braid/commutation presentation.
--
-- Independent local Python/SymPy diagnostics find
--
--   |W(E6) x W(A2)| = 311040
--   |<W(E6)xW(A2), s_glue>| = 696729600 = |W(E8)|.
--
-- Agda records this as a receipt only; Lean native_decide/Python authority is
-- not promoted into an Agda theorem.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

record StructuredE8WeylReceipt : Set where
  constructor structured-e8-weyl-receipt
  field
    structuredRootCount : Nat
    e6TimesA2DiagnosticOrder : Nat
    fullWeylDiagnosticOrder : Nat
    inverseCartanPairingSourceWritten : Bool
    intrinsicGlueRootNormTwoSourceWritten : Bool
    intrinsicGlueReflectionClosureSourceWritten : Bool
    glueReflectionCrossesBranchTypesSourceWritten : Bool
    e8RankEightGramSourceWritten : Bool
    e8GramDeterminantOneSourceWritten : Bool
    e8CoxeterRelationsSourceWritten : Bool
    glueDefinedByLiteralTransport : Bool
    leanKernelReceiptObservedHere : Bool
    agdaIndependentProducerPaidHere : Bool
    note : String
open StructuredE8WeylReceipt public

canonicalStructuredE8WeylReceipt : StructuredE8WeylReceipt
canonicalStructuredE8WeylReceipt =
  structured-e8-weyl-receipt
    240 311040 696729600
    true true true true true true true
    false false false
    "The previous E6+A2 wall is closed at source level on companion Lean: the glue reflection is reconstructed from structured weight pairing, not literal-E8 transport. Local Python independently verifies the full W(E8) permutation order. Original punctured T5 recognition remains a separate question."
