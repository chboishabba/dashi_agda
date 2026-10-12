module DASHI.Foundations.E6F3PGSpProjectivizationCrossKernelReceiptExact where

------------------------------------------------------------------------
-- CROSS-KERNEL RECEIPT: F3^4 SYMPLECTIC LIFTS -> E6 FIVE-SPACE IMAGE
--
-- Companion Lean PR #58 source-writes a finite closure computation on the six
-- literal four-dimensional lifts already used by the E6 exterior-square bridge.
-- It proves, by `native_decide` on the actual repo matrices:
--
--   * generated four-space closure order = 103680;
--   * another generator expansion adds nothing;
--   * primitive exterior-square kernel is exactly { I , -I };
--   * kernel order = 2;
--   * projective quotient order = 51840.
--
-- The existing five-space same-object bridge already identifies every generated
-- word action with the repository E6 action.  Thus this receipt explains the
-- exact factor-of-two projectivization structurally rather than by comparing
-- group orders.
--
-- AUTHORITY / PROMOTION BOUNDARY:
-- This is a CROSS-PROVER receipt only.  Lean source does not become Agda kernel
-- authority.  Even with the exact ±I kernel and same word action, this owner
-- does not manufacture an abstract PGSp4(3) ~= W(E6) group isomorphism without
-- an explicit same-group equivalence theorem.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

leanRepository : String
leanRepository = "chboishabba/dashi_lean4"

leanPR : Nat
leanPR = 58

leanOwner : String
leanOwner = "Integration/F3E6PGSpClosure.lean"

record PGSpProjectivizationReceipt : Set where
  constructor pgsp-projectivization-receipt
  field
    fourSpaceGeneratedOrder : Nat
    exteriorSquareKernelOrder : Nat
    projectiveQuotientOrder : Nat
open PGSpProjectivizationReceipt public

canonicalReceipt : PGSpProjectivizationReceipt
canonicalReceipt = pgsp-projectivization-receipt 103680 2 51840

record Boundary : Set where
  constructor boundary
  field
    sixLiteralFourSpaceLiftsConsumedByLean : Bool
    fourSpaceClosureOrder103680LeanSourceWritten : Bool
    closureFixedPointLeanSourceWritten : Bool
    kernelExactlyPlusMinusIdentityLeanSourceWritten : Bool
    projectiveQuotientOrder51840LeanSourceWritten : Bool
    fiveSpaceGeneratedWordActionSameAsRepoE6AlreadyPaid : Bool
    leanExactHeadKernelReceiptObserved : Bool
    agdaFourSpaceClosureKernelReplayPaid : Bool
    abstractPGSp4EqualsWE6Paid : Bool
open Boundary public

canonicalBoundary : Boundary
canonicalBoundary =
  boundary
    true true true true true true
    false false false
