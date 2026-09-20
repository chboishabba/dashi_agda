module DASHI.Analysis.RiemannG2NormalizedCenteredOffShellLeanDonorExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- NORMALIZED CENTERED OFF SHELL DONOR
--
-- Companion Lean source now owns the exact normalization of the literal
-- centered reflection-pair kernel for the quantitative canonical taper.
--
-- With
--
--   v     = t u,
--   q     = delta / t,
--   alpha = a / t,
--   r     = t / 16,
--
-- the centered factor becomes exactly
--
--   cos(r u) - 1 = cos(v/16) - 1,
--
-- and the literal pair response at delta=q t satisfies
--
--   integral_u K_t(u,delta)
--     = (1/t) integral_v
--         4 G_t^center(v)
--           cosh((a/t)v)
--           cos(q v).
--
-- The canonical shrinking support |u| < 9*pi/(4t) becomes the fixed normalized
-- support |v| < 9*pi/4.
--
-- This is the correct H2 coordinate system.  It does NOT yet prove the shell
-- sum is dominated by the already-constructed Gamma deficit; that remaining
-- theorem is now a fixed-support oscillatory/Fourier shell estimate rather than
-- another C^2-curvature envelope.
------------------------------------------------------------------------

record NormalizedCenteredOffShellReceipt : Set where
  constructor normalized-centered-off-shell-receipt
  field
    repository : String
    branch : String
    sourcePath : String
    pointwiseTheorem : String
    integralTheorem : String
    gapFrequencyTheorem : String
    sourceCommit : String
    rootWiringCommit : String

open NormalizedCenteredOffShellReceipt public

currentNormalizedCenteredOffShellReceipt :
  NormalizedCenteredOffShellReceipt
currentNormalizedCenteredOffShellReceipt =
  normalized-centered-off-shell-receipt
    "chboishabba/dashi_lean4"
    "agent/rh-farshell-quartic-bypass"
    "Synthesis/RiemannNormalizedCenteredOffShell.lean"
    "Synthesis.reflectionPairWeight_centeredCanonical_normalized"
    "Synthesis.integral_reflectionPairWeight_centeredCanonical_normalized"
    "Synthesis.integral_reflectionPairWeight_centeredCanonical_gap_q"
    "480afa0896edb04bf30814d1123f1ecba268dec9"
    "ec396d434ebf3c4d458c66f6a99a85cb75a4b591"

record NormalizedCenteredOffShellBoundary : Set where
  constructor normalized-centered-off-shell-boundary
  field
    exactPointwiseNormalizationSourceWritten : Bool
    exactIntegralNormalizationSourceWritten : Bool
    canonicalSupportBecomesFixedNormalizedWindow : Bool
    shellGapBecomesDimensionlessFrequency : Bool

    oldCurvatureEnvelopeCanonicalForH2 : Bool
    quarticCutoffReusableInsideSignedWindow : Bool

    normalizedIntermediateShellEstimatePaid : Bool
    gammaDeficitDominatesNormalizedShellPaid : Bool
    leanKernelReceiptOwnedHere : Bool
    transportedIntoAgda : Bool
    r2ClosedHere : Bool
    rhDerivedHere : Bool

open NormalizedCenteredOffShellBoundary public

canonicalNormalizedCenteredOffShellBoundary :
  NormalizedCenteredOffShellBoundary
canonicalNormalizedCenteredOffShellBoundary =
  normalized-centered-off-shell-boundary
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
    false

normalizedShellIsActiveH2Coordinates :
  NormalizedCenteredOffShellBoundary.oldCurvatureEnvelopeCanonicalForH2
    canonicalNormalizedCenteredOffShellBoundary ≡ false
normalizedShellIsActiveH2Coordinates = refl

normalizedShellEstimateStillOpen :
  NormalizedCenteredOffShellBoundary.normalizedIntermediateShellEstimatePaid
    canonicalNormalizedCenteredOffShellBoundary ≡ false
normalizedShellEstimateStillOpen = refl
