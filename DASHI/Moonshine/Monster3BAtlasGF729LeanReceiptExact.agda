module DASHI.Moonshine.Monster3BAtlasGF729LeanReceiptExact where

------------------------------------------------------------------------
-- CROSS-PROVER RECEIPT: ATLAS X6 COMPRESSION <-> SELECTED GF(729) ACTION
--
-- Companion Lean branch `agent/e6-f3-exterior-square-maxcut-20261006` now
-- source-writes the literal six-dimensional F3 matrices from the exact producer:
--
--   compressionT,
--   selectedMulBeta,
--   intertwinerQ,
--   intertwinerQInv.
--
-- It states the finite theorems
--
--   compression_selected_action_intertwines :
--     Q * T = M_beta * Q
--
--   intertwiner_left_inverse  : Q^-1 * Q = I
--   intertwiner_right_inverse : Q * Q^-1 = I
--
-- and a solved conjugacy theorem, all by `native_decide` over ZMod 3.
--
-- This Agda file is deliberately a CROSS-PROVER receipt.  It does not convert
-- Lean source into Agda kernel authority, and it distinguishes source-written
-- theorem code from an observed exact-head Lean build receipt.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

leanRepository : String
leanRepository = "chboishabba/dashi_lean4"

leanBranch : String
leanBranch = "agent/e6-f3-exterior-square-maxcut-20261006"

leanOwnerPath : String
leanOwnerPath = "Integration/Monster3BAtlasGF729SameObject.lean"

leanRegressionPath : String
leanRegressionPath = "Integration/Monster3BAtlasGF729SameObjectRegression.lean"

leanIntertwiningTheorem : String
leanIntertwiningTheorem = "compression_selected_action_intertwines"

leanLeftInverseTheorem : String
leanLeftInverseTheorem = "intertwiner_left_inverse"

leanRightInverseTheorem : String
leanRightInverseTheorem = "intertwiner_right_inverse"

record Monster3BGF729LeanReceiptBoundary : Set where
  constructor monster3b-gf729-lean-receipt-boundary
  field
    exactProducerCompressionCoordinatesPaid : Bool
    exactProducerSelectedGF729CoordinatesPaid : Bool
    leanLiteralMatricesSourceWritten : Bool
    leanLiteralSameActionSourceWritten : Bool
    leanExplicitTwoSidedInverseSourceWritten : Bool
    leanSolvedConjugacySourceWritten : Bool
    leanExactHeadKernelReceiptObserved : Bool
    agdaLiteralMatrixReplayPaid : Bool
    polynomialIrreducibilityReprovedInLean : Bool
    fullMonsterActionOrbitStabilizerRecognitionPaid : Bool
open Monster3BGF729LeanReceiptBoundary public

canonicalBoundary : Monster3BGF729LeanReceiptBoundary
canonicalBoundary =
  monster3b-gf729-lean-receipt-boundary
    true
    true
    true
    true
    true
    true
    false
    false
    false
    false
