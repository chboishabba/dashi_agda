module DASHI.Foundations.E6F3ProjectiveStrataCrossKernelReceiptExact where

------------------------------------------------------------------------
-- CROSS-KERNEL RECEIPT: PROJECTIVE QUADRATIC STRATA IN PG(4,3)
--
-- Companion Lean PR #58 now source-writes the complete projectivized
-- stratification of the SAME standard F3^5 quadratic carrier:
--
--   Q=0 : 40 points, SRG(40,12,2,4)
--   Q=1 : 45 points, SRG(45,12,3,3)
--   Q=2 : 36 points, SRG(36,15,6,6)
--
-- with exact total 40+45+36=121=|PG(4,3)|.
--
-- The Q=1 graph remains a geometric association object only; no exceptional
-- representation label is promoted from its cardinality or graph parameters.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

leanRepository : String
leanRepository = "chboishabba/dashi_lean4"

leanPR : Nat
leanPR = 58

leanOwner : String
leanOwner = "Integration/E6F3ProjectiveStrataSRG.lean"

record StratumSRG : Set where
  constructor stratum-srg
  field
    vertices : Nat
    degree : Nat
    adjacentCommon : Nat
    nonAdjacentCommon : Nat
open StratumSRG public

qZeroReceipt : StratumSRG
qZeroReceipt = stratum-srg 40 12 2 4

qOneReceipt : StratumSRG
qOneReceipt = stratum-srg 45 12 3 3

qTwoReceipt : StratumSRG
qTwoReceipt = stratum-srg 36 15 6 6

projectiveTotal : Nat
projectiveTotal = 121

record Boundary : Set where
  constructor boundary
  field
    sameStandardF3FiveCarrierConsumed : Bool
    projectivePartition404536LeanSourceWritten : Bool
    projectiveTotal121LeanSourceWritten : Bool
    qZeroSRGLeanSourceWritten : Bool
    qOneSRGLeanSourceWritten : Bool
    qTwoSRGConsumed : Bool
    leanExactHeadKernelReceiptObserved : Bool
    agdaProjectiveStrataProducerKernelPaidHere : Bool
    qOneGraphPromotedToExceptionalRepresentation : Bool
open Boundary public

canonicalBoundary : Boundary
canonicalBoundary =
  boundary true true true true true true false false false
