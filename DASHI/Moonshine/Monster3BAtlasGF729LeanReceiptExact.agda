module DASHI.Moonshine.Monster3BAtlasGF729LeanReceiptExact where

------------------------------------------------------------------------
-- CROSS-PROVER RECEIPT: ATLAS X6 COMPRESSION <-> CENTER-PRESERVING PRIMITIVE
-- GF(729) ACTION
--
-- Companion Lean branch `agent/e6-f3-exterior-square-maxcut-20261006` now
-- source-writes the preferred depth-eight strict-symplectic compression together
-- with multiplication by the selected primitive
--
--   delta=(0,1,0,1,1,0),  ord(delta)=728,
--
-- in the already-selected GF(729), plus explicit Q and Q^-1 on the SAME F3^6
-- carrier.  This replaces the depth-seven multiplier-2 primitive as the
-- canonical same-phase field weld; the depth-seven element remains the useful
-- center-inverting/similitude comparator.
--
-- Lean source contains `native_decide` theorem statements for:
--
--   Q*T = M_delta*Q;
--   Q^-1*Q = I and Q*Q^-1 = I;
--   M_delta^728 = I;
--   no positive power 1..727 equals I;
--   the chosen nonzero seed orbit has cardinality 728;
--   its stabilizer among the 728 powers has cardinality 1.
--
-- This Agda owner records SOURCE-WRITTEN cross-prover authority only.  No
-- exact-head Lean build has been observed in the present environment, and Lean
-- source does not become Agda kernel authority.
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
leanPrimitiveOrderTheorem = "selected_mul_delta_pow_728 / selected_mul_delta_no_positive_power_below_728"

leanPrimitiveOrbitTheorem : String
leanPrimitiveOrbitTheorem = "primitive_orbit_card"

leanPrimitiveStabilizerTheorem : String
leanPrimitiveStabilizerTheorem = "canonical_seed_stabilizer_card"

record Monster3BGF729LeanReceiptBoundary : Set where
  constructor monster3b-gf729-lean-receipt-boundary
  field
    exactProducerCenterPreservingPrimitiveCoordinatesPaid : Bool
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
