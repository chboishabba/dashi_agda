module DASHI.Foundations.E6F3RootLineSRGCrossKernelReceiptExact where

------------------------------------------------------------------------
-- CROSS-KERNEL RECEIPT: PROJECTIVE E6 ROOT-LINE SRG(36,15,6,6)
--
-- Companion Lean PR #58 now source-writes the projective norm-two/root-line
-- carrier on the SAME standard F3^5 quadratic space already used by the E6
-- mod-3 bridge.  It chooses one canonical representative from each antipodal
-- pair and proves by `native_decide` on the literal finite carrier:
--
--   * 36 projective root lines;
--   * orthogonality degree 15;
--   * 6 common neighbours for adjacent pairs;
--   * 6 common neighbours for non-adjacent pairs.
--
-- Thus the literal projective orthogonality graph has parameters
-- SRG(36,15,6,6).  This receipt attaches that producer to the pre-existing
-- Agda E6RootLineGraphReceipt surface without pretending Lean source is an
-- Agda kernel theorem.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

leanRepository : String
leanRepository = "chboishabba/dashi_lean4"

leanPR : Nat
leanPR = 58

leanOwner : String
leanOwner = "Integration/E6ProjectiveRootLineSRG.lean"

record RootLineSRGReceipt : Set where
  constructor root-line-srg-receipt
  field
    vertexCount : Nat
    degree : Nat
    adjacentCommon : Nat
    nonAdjacentCommon : Nat
open RootLineSRGReceipt public

canonicalReceipt : RootLineSRGReceipt
canonicalReceipt = root-line-srg-receipt 36 15 6 6

record Boundary : Set where
  constructor boundary
  field
    sameStandardF3FiveCarrierConsumed : Bool
    antipodalProjectivizationExplicit : Bool
    vertexCount36LeanSourceWritten : Bool
    degree15LeanSourceWritten : Bool
    adjacentCommon6LeanSourceWritten : Bool
    nonAdjacentCommon6LeanSourceWritten : Bool
    srg361566LeanSourceWritten : Bool
    leanExactHeadKernelReceiptObserved : Bool
    agdaRootLineSRGProducerKernelPaidHere : Bool
    srgCreatesPhysicalOrSemanticMechanism : Bool
open Boundary public

canonicalBoundary : Boundary
canonicalBoundary =
  boundary
    true true true true true true true
    false false false
