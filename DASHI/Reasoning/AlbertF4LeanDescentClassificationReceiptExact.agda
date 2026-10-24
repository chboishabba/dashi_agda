module DASHI.Reasoning.AlbertF4LeanDescentClassificationReceiptExact where

------------------------------------------------------------------------
-- CROSS-PROVER RECEIPT: LEAN ORIGINAL-Q ALBERT DESCENT/CLASSIFICATION SOCKET
--
-- Companion Lean PR #52 now types the remaining F4/E6 classification payment
-- as a SAME-object descent adapter.  Its local data distinguish:
--
--   * native rational Albert object;
--   * Q(i) scalar extension carrying the exact split-F4 root grading;
--   * real scalar extension carrying the positive derivation trace-form
--     diagnostic;
--   * one external/formal characteristic-zero group-scheme classification
--     theorem whose conclusions must be transported back to the SAME native
--     Albert derivation / Jordan-aut / cubic-symmetry actions.
--
-- The Lean compiler deliberately does not let the local observations, source
-- receipts, dimensions/root tables or donor inventory synthesize the global
-- classification theorem.
--
-- This Agda owner is status/provenance only.  It imports no Lean proof object
-- and transfers no kernel authority.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

record LeanDescentClassificationReceipt : Set where
  constructor lean-descent-classification-receipt
  field
    sourcePR : Nat
    owner : String
    nativeQObjectPaid : Bool
    qiSplitChartTypedAsScalarExtension : Bool
    realPlaceDiagnosticTypedAsLocalData : Bool
    sameObjectDescentAdapterTyped : Bool
    sameObjectDescentAdapterInhabited : Bool
    originalQF4LieClassificationPaid : Bool
    originalQF4GroupClassificationPaid : Bool
    originalQE6GroupClassificationPaid : Bool
    crossKernelProofAuthorityTransferred : Bool
open LeanDescentClassificationReceipt public

canonicalBoundary : LeanDescentClassificationReceipt
canonicalBoundary = lean-descent-classification-receipt
  52
  "Integration/RationalAlbertF4E6DescentClassification.lean"
  true true true true
  false false false false false

record Boundary : Set where
  constructor boundary
  field
    leanDescentAdapterObserved : Bool
    leanDescentAdapterInhabited : Bool
    leanOriginalQF4Paid : Bool
    leanOriginalQE6Paid : Bool
    agdaNativeSplitRootDataStillIndependent : Bool
    crossKernelProofAuthorityTransferred : Bool
open Boundary public

canonicalReceiptBoundary : Boundary
canonicalReceiptBoundary = boundary
  canonicalBoundary.sameObjectDescentAdapterTyped
  canonicalBoundary.sameObjectDescentAdapterInhabited
  canonicalBoundary.originalQF4GroupClassificationPaid
  canonicalBoundary.originalQE6GroupClassificationPaid
  true
  canonicalBoundary.crossKernelProofAuthorityTransferred
