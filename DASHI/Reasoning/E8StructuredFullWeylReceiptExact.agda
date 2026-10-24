module DASHI.Reasoning.E8StructuredFullWeylReceiptExact where

------------------------------------------------------------------------
-- CROSS-KERNEL RECEIPT: STRUCTURED 240 -> INTRINSIC E8 WEYL ROOT DATUM
--
-- Synced verbatim in substance from PR #1098 so this geometric-reasoning
-- branch reuses the existing Weyl owner rather than creating a parallel action
-- ontology. Companion Lean source reconstructs the E6+A2 bilinear form from
-- inverse Cartan data, selects a mixed norm-two glue root, and defines the
-- cross-branch reflection intrinsically from that pairing.
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
    "Existing PR #1098 structured-E8 receipt reused: intrinsic glue reflection closes the structured 240 under the E8 Coxeter presentation; local Python independently verifies full W(E8) permutation order 696729600. Agda does not promote the Lean/Python receipt to an independent kernel proof."
