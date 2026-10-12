module DASHI.Moonshine.Monster3BAtlasGF729LeanReceiptExact where

------------------------------------------------------------------------
-- CROSS-PROVER RECEIPT: ATLAS X6 COMPRESSION <-> SELECTED PRIMITIVE GF(729)
-- ACTION
--
-- Companion Lean branch `agent/e6-f3-exterior-square-maxcut-20261006` now
-- source-writes the preferred depth-seven source compression together with the
-- literal selected-GF(729) multiplication matrix M_gamma and an explicit Q,
-- Q^-1 on the same six-dimensional F3 carrier.
--
-- Lean source now contains theorem statements (proved there by `native_decide`)
-- for:
--
--   Q*T = M_gamma*Q;
--   Q^-1*Q = I and Q*Q^-1 = I;
--   M_gamma^728 = I;
--   no positive power 1..727 equals I;
--   the chosen nonzero seed orbit has cardinality 728;
--   its stabilizer among the 728 powers has cardinality 1.
--
-- This is stronger than the earlier depth-five beta/order-364 weld.  The Agda
-- receipt keeps Lean SOURCE-WRITTEN authority separate from an observed
-- exact-head Lean kernel build.  The latter remains false in the present tool
-- environment.
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

leanPrimitiveOrderTheorem : String
leanPrimitiveOrderTheorem = "selected_mul_gamma_pow_728 / selected_mul_gamma_no_positive_power_below_728"

leanPrimitiveOrbitTheorem : String
leanPrimitiveOrbitTheorem = "primitive_orbit_card"

leanPrimitiveStabilizerTheorem : String
leanPrimitiveStabilizerTheorem = "canonical_seed_stabilizer_card"

record Monster3BGF729LeanReceiptBoundary : Set where
  constructor monster3b-gf729-lean-receipt-boundary
  field
    exactProducerPreferredPrimitiveCoordinatesPaid : Bool
    exactProducerPrimitiveOrder728Paid : Bool
    exactProducerPuncturedOrbit728Paid : Bool
    exactProducerPuncturedStabilizerTrivialPaid : Bool
    leanLiteralMatricesSourceWritten : Bool
    leanLiteralSameActionSourceWritten : Bool
    leanExplicitTwoSidedInverseSourceWritten : Bool
    leanPrimitiveOrder728SourceWritten : Bool
    leanPuncturedOrbit728SourceWritten : Bool
    leanPuncturedStabilizerTrivialSourceWritten : Bool
    leanExactHeadKernelReceiptObserved : Bool
    agdaLiteralMatrixReplayPaid : Bool
    fullMonsterSemanticActionRecognitionPaid : Bool
open Monster3BGF729LeanReceiptBoundary public

canonicalBoundary : Monster3BGF729LeanReceiptBoundary
canonicalBoundary =
  monster3b-gf729-lean-receipt-boundary
    true true true true
    true true true true true true
    false false false
