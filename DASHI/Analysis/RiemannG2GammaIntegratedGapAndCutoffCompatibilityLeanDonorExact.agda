module DASHI.Analysis.RiemannG2GammaIntegratedGapAndCutoffCompatibilityLeanDonorExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- INTEGRATED GAMMA GAP + SIGN-WINDOW / QUARTIC-CUTOFF COMPATIBILITY
--
-- Companion Lean now owns the H1 side of the paired-window argument:
--
--   d(t) = R_t(7*pi/(4t)) - R_t(5*pi/(4t)) > 0
--
-- and every matched inner/outer coordinate inherits that explicit uniform
-- ratio gap.  The gap is also integrated against arbitrary nonnegative
-- integrable weights supported in the canonical inner window, and a separate
-- endpoint-sandwich theorem converts pole cancellation into the quantitative
-- centered Gamma deficit without pretending that an integrated mass is a
-- single pointwise ratio times a pole mass.
--
-- The same Lean branch also proves an essential compatibility obstruction:
-- with canonical support Lambda = 9*pi/(4t), the centered near-pair sign
-- condition
--
--   J * Lambda <= pi/2
--
-- forces
--
--   J <= 2t/9.
--
-- Therefore a quartic cutoff J >= t^4 cannot simply replace the signed-window
-- cutoff.  To use the quartic/adaptive far-shell donor one must additionally
-- control the intermediate shell beyond the sign window, or derive a sharper
-- far-tail theorem at a sign-compatible cutoff.
------------------------------------------------------------------------

record GammaIntegratedGapCutoffCompatibilityReceipt : Set where
  constructor gamma-integrated-gap-cutoff-compatibility-receipt
  field
    repository : String
    branch : String
    ratioGapPath : String
    integratedGapPath : String
    integratedDeficitPath : String
    cutoffCompatibilityPath : String
    ratioGapBlob : String
    integratedGapBlob : String
    integratedDeficitBlob : String
    cutoffCompatibilityCommit : String

open GammaIntegratedGapCutoffCompatibilityReceipt public

currentGammaIntegratedGapCutoffCompatibilityReceipt :
  GammaIntegratedGapCutoffCompatibilityReceipt
currentGammaIntegratedGapCutoffCompatibilityReceipt =
  gamma-integrated-gap-cutoff-compatibility-receipt
    "chboishabba/dashi_lean4"
    "agent/rh-farshell-quartic-bypass"
    "Synthesis/RiemannGammaCanonicalRatioGap.lean"
    "Synthesis/RiemannGammaIntegratedRatioGap.lean"
    "Synthesis/RiemannGammaCanonicalIntegratedDeficit.lean"
    "Synthesis/RiemannFarShellSignedWindowQuarticIncompatibility.lean"
    "70629f76015dc688d7048cc9b75adb184bcd0e19"
    "e2fecc46a558e52f95a9a13d5909956302e348a4"
    "0c748c59d8329d39db3263be547da7733797b62b"
    "8a2e9e8f6227cf5c9b4ef13c4e062e77755580ee"

record GammaIntegratedGapCutoffCompatibilityBoundary : Set where
  constructor gamma-integrated-gap-cutoff-compatibility-boundary
  field
    canonicalRatioGapPositiveSourceWritten : Bool
    matchedCoordinateUniformGapSourceWritten : Bool
    integratedNonnegativeWeightGapSourceWritten : Bool
    integratedPoleCancellationGammaDeficitSourceWritten : Bool

    signedWindowForcesLinearCutoffSourceWritten : Bool
    quarticCutoffInsideSameSignedWindowRejectedSourceWritten : Bool

    h1IntegratedRatioGapPaid : Bool
    oldNaturalSignedWindowEnvelopeCanCloseH2 : Bool
    quarticFarTailCanBeSubstitutedWithoutIntermediateShell : Bool

    intermediateShellControlStillRequiredForQuarticRoute : Bool
    sharperSignCompatibleFarTailWouldAlsoSufficeStructurally : Bool

    leanKernelReceiptOwnedHere : Bool
    transportedIntoAgdaKernelHere : Bool
    h2ClosedHere : Bool
    r2ClosedHere : Bool
    rhDerivedHere : Bool

open GammaIntegratedGapCutoffCompatibilityBoundary public

canonicalGammaIntegratedGapCutoffCompatibilityBoundary :
  GammaIntegratedGapCutoffCompatibilityBoundary
canonicalGammaIntegratedGapCutoffCompatibilityBoundary =
  gamma-integrated-gap-cutoff-compatibility-boundary
    true
    true
    true
    true

    true
    true

    true
    false
    false

    true
    true

    false
    false
    false
    false
    false

h1IsNoLongerOpen :
  GammaIntegratedGapCutoffCompatibilityBoundary.h1IntegratedRatioGapPaid
    canonicalGammaIntegratedGapCutoffCompatibilityBoundary ≡ true
h1IsNoLongerOpen = refl

quarticNeedsANewShellArgument :
  GammaIntegratedGapCutoffCompatibilityBoundary.intermediateShellControlStillRequiredForQuarticRoute
    canonicalGammaIntegratedGapCutoffCompatibilityBoundary ≡ true
quarticNeedsANewShellArgument = refl

rhStillFailClosed :
  GammaIntegratedGapCutoffCompatibilityBoundary.rhDerivedHere
    canonicalGammaIntegratedGapCutoffCompatibilityBoundary ≡ false
rhStillFailClosed = refl
