module DASHI.Foundations.E6F3LiteralRootLineSameObjectCrossKernelReceiptExact where

------------------------------------------------------------------------
-- CROSS-KERNEL RECEIPT: LITERAL E6 ROOTS -> PROJECTIVE Q=2 ROOT LINES
--
-- Companion Lean PR #58 now projectivizes the repo's actual finite E6 root
-- carrier, transports it through the existing mod-3 quotient/isometry, and
-- source-writes:
--
--   * 36 canonical literal E6 root lines;
--   * a two-sided equivalence with the existing 36 Q=2 projective root lines;
--   * equality of the mod-3 Cartan pairing with the standard F3^5 dot form;
--   * SRG(36,15,6,6) on the literal projective E6 root carrier.
--
-- This receipt records Lean ownership/status only.  It does not pretend the
-- Lean source is an Agda kernel proof and it preserves the no-cardinality-
-- promotion firewall.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

leanRepository : String
leanRepository = "chboishabba/dashi_lean4"

leanPR : Nat
leanPR = 58

leanOwner : String
leanOwner = "Integration/E6RootLineSameObject.lean"

record Receipt : Set where
  constructor receipt
  field
    literalRootLineCount : Nat
    degree : Nat
    commonNeighborCount : Nat
open Receipt public

canonicalReceipt : Receipt
canonicalReceipt = receipt 36 15 6

record Boundary : Set where
  constructor boundary
  field
    literalE6RootCarrierConsumed : Bool
    antipodalProjectivizationExplicit : Bool
    literalRootLineQTwoEquivalenceLeanSourceWritten : Bool
    cartanDotIntertwiningLeanSourceWritten : Bool
    literalRootLineSRGLeanSourceWritten : Bool
    leanExactHeadKernelReceiptObserved : Bool
    agdaSameObjectProducerKernelPaidHere : Bool
    cardinalityAlonePromotesSameObject : Bool
open Boundary public

canonicalBoundary : Boundary
canonicalBoundary =
  boundary true true true true true false false false
