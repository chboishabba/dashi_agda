module DASHI.Analysis.RiemannG2ProjectiveOffNormalizedAtomicCarrierLeanDonorExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- NORMALIZED ATOMIC CARRIERS FOR ALL THREE PROJECTIVE OFF PIECES
--
-- Companion Lean now has exact normalized finite atomic realizations for:
--
--   1. the centered Off response at r=t/16;
--   2. the centered Off response at 2r=t/8;
--   3. the radius-zero Off base response.
--
-- Together with the exact projective decomposition
--
--   D_off^proj
--     = C_cent(2r) A0(r)
--       - C_cent(r) A0(2r)
--       + C(0) [A0(r)-A0(2r)],
--
-- every projective Off ingredient is now represented on a normalized literal
-- zero carrier at the finite-aggregate level.
--
-- The remaining same-object seam is the infinite carrier:
--   * transport these finite normalized identities through the actual
--     reflection-pair tsum indexing used by offOrdProjectiveDefect;
--   * preserve the signed combination;
--   * then attach the RvM/Fourier estimate to that exact projective consumer.
------------------------------------------------------------------------

record ProjectiveOffNormalizedAtomicReceipt : Set where
  constructor projective-off-normalized-atomic-receipt
  field
    repository : String
    branch : String
    projectiveBridgePath : String
    twoRadiusPath : String
    radiusZeroPath : String
    projectiveOffTheorem : String
    secondRadiusTheorem : String
    radiusZeroPairTheorem : String
    radiusZeroFiniteSumTheorem : String
    projectiveBridgeCommit : String
    twoRadiusCommit : String
    radiusZeroCommit : String

open ProjectiveOffNormalizedAtomicReceipt public

currentProjectiveOffNormalizedAtomicReceipt :
  ProjectiveOffNormalizedAtomicReceipt
currentProjectiveOffNormalizedAtomicReceipt =
  projective-off-normalized-atomic-receipt
    "chboishabba/dashi_lean4"
    "agent/rh-farshell-quartic-bypass"
    "Synthesis/RiemannProjectiveCenteredGaugeBridge.lean"
    "Synthesis/RiemannNormalizedCenteredOffTwoRadius.lean"
    "Synthesis/RiemannNormalizedOffRadiusZeroAtomicMeasure.lean"
    "Synthesis.offOrdProjectiveDefect_eq_twoCentered_plus_base"
    "Synthesis.integral_reflectionPairWeight_centeredCanonical_twoRadius_normalized"
    "Synthesis.literal_radiusZero_pair_eq_one_div_t_mul_normalizedAtom"
    "Synthesis.sum_literal_radiusZero_pairs_eq_normalizedAtoms"
    "4e32b1897550480f40eb8a0957a0b619f142244e"
    "8e6da2406d1e93541874e55ccc68817f2346a031"
    "237c517c3eda9f30cb7f8782122625a3fa978ce6"

record ProjectiveOffNormalizedAtomicBoundary : Set where
  constructor projective-off-normalized-atomic-boundary
  field
    exactProjectiveThreePieceDecompositionSourceWritten : Bool
    centeredFirstRadiusNormalizedFiniteCarrierPaid : Bool
    centeredSecondRadiusNormalizedFiniteCarrierPaid : Bool
    radiusZeroNormalizedFiniteCarrierPaid : Bool

    literalInfiniteReflectionPairTsumAttachmentPaid : Bool
    signedProjectiveRvMAttachmentPaid : Bool
    projectiveOffAnalyticBoundPaid : Bool

    leanKernelReceiptOwnedHere : Bool
    transportedIntoAgda : Bool
    rhDerivedHere : Bool

open ProjectiveOffNormalizedAtomicBoundary public

canonicalProjectiveOffNormalizedAtomicBoundary :
  ProjectiveOffNormalizedAtomicBoundary
canonicalProjectiveOffNormalizedAtomicBoundary =
  projective-off-normalized-atomic-boundary
    true
    true
    true
    true

    false
    false
    false

    false
    false
    false

allFiniteProjectiveOffPiecesNormalized :
  ProjectiveOffNormalizedAtomicBoundary.radiusZeroNormalizedFiniteCarrierPaid
    canonicalProjectiveOffNormalizedAtomicBoundary ≡ true
allFiniteProjectiveOffPiecesNormalized = refl

infiniteProjectiveTsumStillOpen :
  ProjectiveOffNormalizedAtomicBoundary.literalInfiniteReflectionPairTsumAttachmentPaid
    canonicalProjectiveOffNormalizedAtomicBoundary ≡ false
infiniteProjectiveTsumStillOpen = refl
