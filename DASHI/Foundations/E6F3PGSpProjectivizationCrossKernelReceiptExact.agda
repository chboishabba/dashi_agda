module DASHI.Foundations.E6F3PGSpProjectivizationCrossKernelReceiptExact where

------------------------------------------------------------------------
-- CROSS-KERNEL RECEIPT: F3^4 SYMPLECTIC LIFTS -> E6 FIVE-SPACE IMAGE
--
-- Companion Lean PR #58 source-writes the finite closure computation on the
-- six literal four-dimensional lifts already used by the E6 exterior-square
-- bridge.  The closure owner pays:
--
--   * generated four-space closure order = 103680;
--   * another generator expansion adds nothing;
--   * primitive exterior-square kernel is exactly { I , -I };
--   * kernel order = 2;
--   * projective quotient order = 51840.
--
-- The same Lean branch now also source-writes the stronger finite same-image
-- theorem on the literal matrices:
--
--   projectiveFiveImage = e6GeneratedClosure
--
-- where each side has exactly 51840 5x5 matrices.  This is stronger than an
-- order comparison: after the already-paid generator intertwining, the induced
-- exterior-square five-space image and the repository E6 Weyl image are the
-- SAME finite matrix subset of the SAME five-space endomorphism carrier.
--
-- It now goes one step further and inhabits the pre-existing
-- PGSpWeylRecognition interface at this concrete matrix-image level: the two
-- actor carriers are the equal matrix images, the actor maps are two-sided,
-- and both actors act by the same 5x5 matrix on the same F3^5 carrier.
--
-- AUTHORITY / PROMOTION BOUNDARY:
-- This is a CROSS-PROVER receipt only.  Lean source does not become Agda kernel
-- authority.  Literal same-matrix-image recognition is recorded separately
-- from an abstract named group isomorphism PGSp4(3) ~= W(E6).  The latter still
-- requires explicit abstract quotient/group packaging if we want that named
-- theorem rather than the stronger-for-representation-purposes same-image fact.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

leanRepository : String
leanRepository = "chboishabba/dashi_lean4"

leanPR : Nat
leanPR = 58

leanClosureOwner : String
leanClosureOwner = "Integration/F3E6PGSpClosure.lean"

leanImageRecognitionOwner : String
leanImageRecognitionOwner = "Integration/F3E6PGSpImageRecognition.lean"

record PGSpProjectivizationReceipt : Set where
  constructor pgsp-projectivization-receipt
  field
    fourSpaceGeneratedOrder : Nat
    exteriorSquareKernelOrder : Nat
    projectiveQuotientOrder : Nat
    inducedFiveSpaceImageOrder : Nat
    repoE6FiveSpaceImageOrder : Nat
open PGSpProjectivizationReceipt public

canonicalReceipt : PGSpProjectivizationReceipt
canonicalReceipt = pgsp-projectivization-receipt 103680 2 51840 51840 51840

record Boundary : Set where
  constructor boundary
  field
    sixLiteralFourSpaceLiftsConsumedByLean : Bool
    fourSpaceClosureOrder103680LeanSourceWritten : Bool
    closureFixedPointLeanSourceWritten : Bool
    kernelExactlyPlusMinusIdentityLeanSourceWritten : Bool
    projectiveQuotientOrder51840LeanSourceWritten : Bool
    fiveSpaceGeneratedWordActionSameAsRepoE6AlreadyPaid : Bool
    inducedFiveSpaceImageOrder51840LeanSourceWritten : Bool
    repoE6FiveSpaceImageOrder51840LeanSourceWritten : Bool
    literalFiveSpaceMatrixImageEqualityLeanSourceWritten : Bool
    sameActionMatrixImageRecognitionLeanSourceWritten : Bool
    pgspWeylRecognitionInterfaceInhabitedAtMatrixImageLeanSourceWritten : Bool
    leanExactHeadKernelReceiptObserved : Bool
    agdaFourSpaceClosureKernelReplayPaid : Bool
    agdaLiteralFiveSpaceImageReplayPaid : Bool
    abstractPGSp4EqualsWE6Paid : Bool
open Boundary public

canonicalBoundary : Boundary
canonicalBoundary =
  boundary
    true true true true true true
    true true true true true
    false false false false
