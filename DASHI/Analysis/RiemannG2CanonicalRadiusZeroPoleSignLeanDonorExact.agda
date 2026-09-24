module DASHI.Analysis.RiemannG2CanonicalRadiusZeroPoleSignLeanDonorExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- CANONICAL TAPER RADIUS-ZERO POLE SIGN
--
-- The companion Lean positive-taper constructor is now strengthened to own:
--
--   poleEvenResp g t r = 0
--   0 < poleEvenResp g t 0
--
-- for the same canonical taper and selected positive radius.
--
-- Since the final even-cone pole coordinate at radius zero is
--
--   ell(Q_pole(0)) = -4 * poleEvenResp(g,t,0),
--
-- the radius-zero pole correction is strictly negative.
--
-- This is independent analytic information about the taper construction.
-- It does not by itself pay the signed complement baseline, and the final
-- explicit-formula balance must not be used to manufacture that payment.
------------------------------------------------------------------------

record CanonicalRadiusZeroPoleSignLeanReceipt : Set where
  constructor canonical-radius-zero-pole-sign-lean-receipt
  field
    repository : String
    branch : String
    strengthenedConstructorPath : String
    finalScalarCorollaryPath : String
    strengthenedConstructorCommit : String
    finalScalarCorollaryCommit : String

open CanonicalRadiusZeroPoleSignLeanReceipt public

currentCanonicalRadiusZeroPoleSignLeanReceipt :
  CanonicalRadiusZeroPoleSignLeanReceipt
currentCanonicalRadiusZeroPoleSignLeanReceipt =
  canonical-radius-zero-pole-sign-lean-receipt
    "chboishabba/dashi_lean4"
    "agent/rh-farshell-quartic-bypass"
    "Imported/Zeta23Bridge/Zeta23Bridge/LiteralWeilEvenChannelTaper.lean"
    "Synthesis/RiemannCanonicalTaperRadiusZeroPoleSign.lean"
    "b171d9143affc74a209f661b1a2942bd3b8fa11e"
    "f57816aaea83f739d1af13f419e2085e15f635cd"

record CanonicalRadiusZeroPoleSignBoundary : Set where
  constructor canonical-radius-zero-pole-sign-boundary
  field
    selectedRadiusPoleKilled : Bool
    radiusZeroPoleResponsePositive : Bool
    radiusZeroFinalPoleCorrectionNegative : Bool

    usesFinalBalanceToDerivePoleSign : Bool
    signedComplementBaselinePaid : Bool
    centeredComplementSignPaid : Bool

    leanKernelReceiptOwnedHere : Bool
    transportedIntoAgda : Bool
    r2ClosedHere : Bool
    rhDerivedHere : Bool

open CanonicalRadiusZeroPoleSignBoundary public

canonicalRadiusZeroPoleSignBoundary :
  CanonicalRadiusZeroPoleSignBoundary
canonicalRadiusZeroPoleSignBoundary =
  canonical-radius-zero-pole-sign-boundary
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
