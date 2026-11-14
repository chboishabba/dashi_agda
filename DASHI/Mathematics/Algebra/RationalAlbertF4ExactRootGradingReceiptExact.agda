module DASHI.Mathematics.Algebra.RationalAlbertF4ExactRootGradingReceiptExact where

------------------------------------------------------------------------
-- EXACT ROOT-GRADED LIE-ALGEBRA RECEIPT FOR THE ALBERT DERIVATIONS
--
-- Companion producer:
--   scripts/albert_f4_exact_root_grading_probe.py
--
-- Starting from the exact Q(i) one-dimensional root spaces already selected by
-- symbolic Cartan projectors, the producer checks all C(48,2)=1128 unordered
-- pairs of nonzero roots.  Exact matrix commutators satisfy the full root-
-- grading pattern:
--
--   alpha+beta a root  -> nonzero bracket proportional to g_(alpha+beta): 408
--   beta=-alpha        -> nonzero bracket in the 4-dimensional Cartan:      24
--   otherwise          -> bracket exactly zero:                            696
--
-- This removes the last local ambiguity that the 4+48 decomposition might only
-- share F4 cardinalities without carrying the corresponding root-graded Lie
-- bracket.  The remaining promotion is the general characteristic-zero
-- classification theorem / same-form recognition, not a missing local bracket
-- or root-space calculation.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

record ExactRootGradingReceipt : Set where
  constructor exact-root-grading-receipt
  field
    scriptPath : String
    scalarExtension : String
    rootSpaceCount : Nat
    eachRootSpaceDimension : Nat
    unorderedRootPairsChecked : Nat
    rootSumNonzeroBrackets : Nat
    oppositeRootCartanBrackets : Nat
    forbiddenSumZeroBrackets : Nat
    CartanDimension : Nat
    rootSumTargetsExact : Bool
    oppositeRootsLandInCartanExactly : Bool
    forbiddenSumsBracketZeroExactly : Bool
    floatingPointUsed : Bool
open ExactRootGradingReceipt public

canonicalExactRootGradingReceipt : ExactRootGradingReceipt
canonicalExactRootGradingReceipt =
  exact-root-grading-receipt
    "scripts/albert_f4_exact_root_grading_probe.py"
    "Q(i)"
    48 1
    1128
    408
    24
    696
    4
    true true true false

record Boundary : Set where
  constructor boundary
  field
    exactFortyEightRootSpacesConsumed : Bool
    allUnorderedRootPairsCheckedExactly : Bool
    rootAdditionBracketLawPaidByProducer : Bool
    oppositeRootCartanLawPaidByProducer : Bool
    forbiddenRootSumZeroLawPaidByProducer : Bool
    localF4RootGradedLieStructurePaidByProducer : Bool
    AgdaInternalQIReplayPaid : Bool
    generalClassificationTheoremPaid : Bool
open Boundary public

canonicalBoundary : Boundary
canonicalBoundary =
  boundary true true true true true true false false
