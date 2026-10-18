module DASHI.Analysis.RiemannG2ProjectiveTwoRadiusNormalizedLeanDonorExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- PROJECTIVE OFF -> TWO CENTERED NORMALIZED RADII + BASE
--
-- Companion Lean now pays the exact representation needed to connect the
-- reflection-pair projective cutset to the normalized Fourier/RvM machinery.
--
-- For a scalar channel C and on-line profile A0,
--
--   D_C(r) = C(2r) A0(r) - C(r) A0(2r)
--
-- is rewritten exactly as
--
--   D_C(r)
--     = [C(2r)-C(0)] A0(r)
--       - [C(r)-C(0)] A0(2r)
--       + C(0) [A0(r)-A0(2r)].
--
-- On the literal Off channel,
--
--   C(s)-C(0)
--
-- is exactly the Off response of gammaCenteredTaper g s at sample radius zero.
--
-- The normalized fixed-profile construction is now parameterized by a scale k:
--
--   H_{t,k}(v) = G_t(v) (cos(k v/16)-1).
--
-- Thus k=1 realizes r=t/16 and k=2 realizes the missing projective radius
-- 2r=t/8, both with an exact 1/t Jacobian normalization.
--
-- What remains open is NOT the second radius.  It is:
--   * attach the radius-zero base Off response C(0) to the normalized counting
--     / Fourier carrier;
--   * aggregate the three exact signed pieces onto the literal infinite Off
--     projective defect;
--   * prove the resulting signed/RvM estimate.
------------------------------------------------------------------------

record ProjectiveTwoRadiusNormalizedReceipt : Set where
  constructor projective-two-radius-normalized-receipt
  field
    repository : String
    branch : String
    bridgePath : String
    twoRadiusPath : String
    projectiveDecompositionTheorem : String
    literalOffDecompositionTheorem : String
    secondRadiusNormalizationTheorem : String
    bridgeCommit : String
    twoRadiusCommit : String

open ProjectiveTwoRadiusNormalizedReceipt public

currentProjectiveTwoRadiusNormalizedReceipt :
  ProjectiveTwoRadiusNormalizedReceipt
currentProjectiveTwoRadiusNormalizedReceipt =
  projective-two-radius-normalized-receipt
    "chboishabba/dashi_lean4"
    "agent/rh-farshell-quartic-bypass"
    "Synthesis/RiemannProjectiveCenteredGaugeBridge.lean"
    "Synthesis/RiemannNormalizedCenteredOffTwoRadius.lean"
    "Synthesis.channelProjectiveDefect_eq_centeredRadiusDecomposition"
    "Synthesis.offOrdProjectiveDefect_eq_twoCentered_plus_base"
    "Synthesis.integral_reflectionPairWeight_centeredCanonical_twoRadius_normalized"
    "4e32b1897550480f40eb8a0957a0b619f142244e"
    "8e6da2406d1e93541874e55ccc68817f2346a031"

record ProjectiveTwoRadiusNormalizedBoundary : Set where
  constructor projective-two-radius-normalized-boundary
  field
    exactProjectiveCenteredDecompositionSourceWritten : Bool
    literalOffCenteredIdentityReused : Bool
    firstRadiusNormalizedSourceWritten : Bool
    secondRadiusNormalizedSourceWritten : Bool
    radiusZeroBaseTermExplicit : Bool

    radiusZeroBaseNormalizedCountingAttachmentPaid : Bool
    literalInfiniteProjectiveOffAggregateAttached : Bool
    signedRvMProjectiveEstimatePaid : Bool

    leanKernelReceiptOwnedHere : Bool
    transportedIntoAgda : Bool
    highAnalyticClosurePaid : Bool
    rhDerivedHere : Bool

open ProjectiveTwoRadiusNormalizedBoundary public

canonicalProjectiveTwoRadiusNormalizedBoundary :
  ProjectiveTwoRadiusNormalizedBoundary
canonicalProjectiveTwoRadiusNormalizedBoundary =
  projective-two-radius-normalized-boundary
    true
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
    false

secondProjectiveRadiusNoLongerRepresentationDebt :
  ProjectiveTwoRadiusNormalizedBoundary.secondRadiusNormalizedSourceWritten
    canonicalProjectiveTwoRadiusNormalizedBoundary ≡ true
secondProjectiveRadiusNoLongerRepresentationDebt = refl

radiusZeroBaseIsNextRepresentationSeam :
  ProjectiveTwoRadiusNormalizedBoundary.radiusZeroBaseNormalizedCountingAttachmentPaid
    canonicalProjectiveTwoRadiusNormalizedBoundary ≡ false
radiusZeroBaseIsNextRepresentationSeam = refl
