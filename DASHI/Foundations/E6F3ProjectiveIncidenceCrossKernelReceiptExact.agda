module DASHI.Foundations.E6F3ProjectiveIncidenceCrossKernelReceiptExact where

------------------------------------------------------------------------
-- CROSS-KERNEL RECEIPT: PROJECTIVE LAGRANGIAN / E6-NULL INCIDENCE DUALITY
--
-- Companion Lean PR #58 source-writes the finite projective recognition:
--
--   * 40 canonical projective Lagrangian Pluecker representatives;
--   * 40 canonical primitive null representatives;
--   * 40 canonical standard-E6 null representatives;
--   * explicit two-sided projective transport through the existing
--     primitive-to-standard five-space isometry;
--   * Pluecker meet-incidence iff standard quadratic orthogonality;
--   * exact projective association graph SRG(40,12,2,4), with source/target
--     adjacency intertwined by the same-object map.
--
-- This is stronger than 40=40: it identifies the same projective incidence
-- geometry under an explicit same-object map. Raw punctured T4 remains a
-- distinct 80-state carrier; the exceptional 80-state source is the derived
-- oriented Lagrangian-bivector carrier.
--
-- AUTHORITY BOUNDARY
-- ------------------
-- Lean source is cross-prover evidence only. It does not become an Agda
-- kernel theorem. This owner records exactly what the companion source says
-- and leaves an Agda-native inhabitant of ProjectiveIncidenceRecognition / the
-- SRG receipt as a separate kernel obligation if desired.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

leanRepository : String
leanRepository = "chboishabba/dashi_lean4"

leanPR : Nat
leanPR = 58

leanOwner : String
leanOwner = "Integration/F3E6ProjectiveIncidenceDuality.lean"

record ProjectiveIncidenceReceipt : Set where
  constructor projective-incidence-receipt
  field
    projectiveLagrangianCount : Nat
    projectivePrimitiveNullCount : Nat
    projectiveStandardNullCount : Nat
    projectiveDegree : Nat
    projectiveAdjacentCommon : Nat
    projectiveNonAdjacentCommon : Nat
open ProjectiveIncidenceReceipt public

canonicalReceipt : ProjectiveIncidenceReceipt
canonicalReceipt = projective-incidence-receipt 40 40 40 12 2 4

record Boundary : Set where
  constructor boundary
  field
    projectiveLagrangianCount40LeanSourceWritten : Bool
    projectivePrimitiveNullCount40LeanSourceWritten : Bool
    projectiveStandardNullCount40LeanSourceWritten : Bool
    primitiveLagNullSameObjectLeanSourceWritten : Bool
    projectiveLagStandardNullEquivalenceLeanSourceWritten : Bool
    plueckerMeetEqualsPrimitivePolarLeanSourceWritten : Bool
    incidenceOrthogonalityEquivalenceLeanSourceWritten : Bool
    projectiveSRG401224LeanSourceWritten : Bool
    sourceTargetAdjacencyIntertwiningLeanSourceWritten : Bool
    leanExactHeadKernelReceiptObserved : Bool
    agdaProjectiveIncidenceKernelReplayPaid : Bool
    agdaProjectiveSRGKernelReplayPaid : Bool
    rawPuncturedT4PromotedToLagCarrier : Bool
    cardinalityAlonePromotesProjectiveRecognition : Bool
open Boundary public

canonicalBoundary : Boundary
canonicalBoundary =
  boundary
    true true true true true true true true true
    false false false false false

end DASHI.Foundations.E6F3ProjectiveIncidenceCrossKernelReceiptExact
