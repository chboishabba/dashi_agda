module DASHI.Analysis.RiemannG2CenteredGammaQuadraticLeanDonorExact where

------------------------------------------------------------------------
-- CENTERED GAMMA / FINAL COMPLEMENT QUADRATIC DONOR
--
-- Instead of bounding the two Gamma samples independently, companion Lean source
-- proves the exact centering identity with
--
--   h_r(u) = g(u) (cos(ru)-1):
--
--   Gamma_g(t,r)+Gamma_g(t,-r)-2 Gamma_g(t,0)
--     = 2 Gamma_{h_r}(t,0).
--
-- It then proves
--
--   |h_r|      <= r^2 * (Lambda^2/2) |g|
--   |h_r'|     <= r^2 * ((Lambda^2/2)|g'| + Lambda|g|)
--   |h_r''|    <= r^2 * ((Lambda^2/2)|g''| + 2Lambda|g'| + |g|)
--
-- and hence
--
--   stripConst(sampleTest h_r t 0, Lambda)
--     <= r^2 * centeredStripCoeff(g,Lambda,t).
--
-- Therefore the centered Gamma correction is O(r^2) without paying the raw
-- shrinking-support ||g''||_1 norm.  A further companion theorem proves the same
-- centering for the final universal Off response and combines the two into a
-- final-carrier centered Off+Gamma O(r^2) correction.
--
-- The remaining semantic issue is the radius-zero baseline: this donor controls
-- the correction away from radius zero; it does not identify the radius-zero
-- joint complement with the final baselineCluster payment by itself.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

record CenteredGammaQuadraticLeanReceipt : Set where
  constructor centered-gamma-quadratic-lean-receipt
  field
    repository : String
    branch : String

    centeredIdentityPath : String
    centeredMassPath : String
    centeredPointwisePath : String
    centeredStripPath : String
    centeredEnvelopePath : String
    finalComplementPath : String
    regressionPath : String

    centeredIdentityCommit : String
    centeredMassCommit : String
    centeredPointwiseCommit : String
    centeredStripCommit : String
    centeredEnvelopeCommit : String
    finalComplementCommit : String
    regressionCommit : String

open CenteredGammaQuadraticLeanReceipt public

currentCenteredGammaQuadraticLeanReceipt :
  CenteredGammaQuadraticLeanReceipt
currentCenteredGammaQuadraticLeanReceipt =
  centered-gamma-quadratic-lean-receipt
    "chboishabba/dashi_lean4"
    "agent/rh-farshell-quartic-bypass"

    "Synthesis/RiemannGammaCenteredConeExact.lean"
    "Synthesis/RiemannGammaCenteredQuadraticMass.lean"
    "Synthesis/RiemannGammaCenteredQuadraticPointwise.lean"
    "Synthesis/RiemannGammaCenteredQuadraticStrip.lean"
    "Synthesis/RiemannGammaCenteredQuadraticEnvelope.lean"
    "Synthesis/RiemannFinalComplementCenteredQuadratic.lean"
    "Synthesis/RiemannGammaCenteredQuadraticRegression.lean"

    "582825abd2db87ba3822e56fdc1b9a3a42dcabbc"
    "7f7134b3eb890463dd49d1a85b01da3e5e0c74f7"
    "fab4b47c80cdd587bc4cb714a1f86aca65940bb9"
    "636677ff12bda68bc7fd747b00606fe9d54f8bf6"
    "8a268d57dbe030a76146e5321cd7d416c830605c"
    "dec899ad449ed1fe09da35392e663802b2035f36"
    "75f8d241739ac3a88cdf6731e7bef235f03216aa"

record CenteredGammaQuadraticDonorBoundary : Set where
  constructor centered-gamma-quadratic-donor-boundary
  field
    exactGammaCenteringIdentitySourceWritten : Bool
    centeredTaperMassQuadraticSourceWritten : Bool
    centeredTaperFirstDerivativeQuadraticSourceWritten : Bool
    centeredTaperSecondDerivativeQuadraticSourceWritten : Bool
    centeredStripConstantQuadraticSourceWritten : Bool
    centeredGammaCorrectionQuadraticSourceWritten : Bool
    finalOffCorrectionQuadraticSourceWritten : Bool
    finalJointOffGammaCorrectionQuadraticSourceWritten : Bool

    projectiveBalanceImported : Bool
    finalUniversalResponseUsed : Bool
    rawShrinkingSupportSecondDerivativePenaltyIntrinsicToCorrection : Bool

    radiusZeroJointBaselineStillRequiresIdentification : Bool
    finiteNearSignedCoreStillRequiresControl : Bool

    leanKernelReceiptOwnedHere : Bool
    transportedIntoAgda : Bool
    finalGammaBudgetClosedHere : Bool
    r2ClosedHere : Bool
    rhDerivedHere : Bool

open CenteredGammaQuadraticDonorBoundary public

canonicalCenteredGammaQuadraticDonorBoundary :
  CenteredGammaQuadraticDonorBoundary
canonicalCenteredGammaQuadraticDonorBoundary =
  centered-gamma-quadratic-donor-boundary
    true
    true
    true
    true
    true
    true
    true
    true
    false
    true
    false
    true
    true
    false
    false
    false
    false
    false
