module DASHI.Analysis.RiemannG2NormalizedCenteredOffOscillatoryDecayLeanDonorExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- NORMALIZED CENTERED OFF-SHELL OSCILLATORY DECAY
--
-- Companion Lean now pushes H2d past the mere coordinate normalization.
--
-- First it proves that after v=t*u the canonical shrinking taper is literally
-- a fixed two-window affine profile:
--
--   inner(v) =
--     psi(4(v-pi)/pi) + psi(-4(v+pi)/pi)
--
--   outer(v) =
--     psi(4(v-2pi)/pi) + psi(-4(v+2pi)/pi),
--
-- with only the bounded scalar mixing coefficient lambda(t) left variable.
--
-- For the centered profile H_t(v), define
--
--   W_{t,alpha}(v) = 4 H_t(v) cosh(alpha v).
--
-- The existing signed oscillatory integration-by-parts theorem is then applied
-- in the NORMALIZED coordinate:
--
--   | integral W_{t,alpha}(v) cos(qv) dv |
--      <= C_norm(t,alpha) / q^2
--
-- for q != 0, where C_norm is the L1 mass of the second derivative of the
-- fixed-support normalized pair weight.
--
-- Transporting through the exact v=t*u normalization and delta=q*t gives
--
--   | integral K_t(u;a,delta) du |
--      <= (1/t) * C_norm(t,a/t) / q^2.
--
-- This removes the old shrinking-support curvature blow-up from the per-pair
-- H2d theorem.  The remaining hard step is to SUM these signed/frequency-local
-- bounds (or exploit stronger aggregate cancellation) against the literal zero
-- carrier strongly enough to beat the already-paid Gamma deficit.
------------------------------------------------------------------------

record NormalizedCenteredOffOscillatoryDecayReceipt : Set where
  constructor normalized-centered-off-oscillatory-decay-receipt
  field
    repository : String
    branch : String
    fixedProfilePath : String
    decayPath : String
    fixedProfileCommit : String
    decayCommit : String
    rootWiringCommit : String

open NormalizedCenteredOffOscillatoryDecayReceipt public

currentNormalizedCenteredOffOscillatoryDecayReceipt :
  NormalizedCenteredOffOscillatoryDecayReceipt
currentNormalizedCenteredOffOscillatoryDecayReceipt =
  normalized-centered-off-oscillatory-decay-receipt
    "chboishabba/dashi_lean4"
    "agent/rh-farshell-quartic-bypass"
    "Synthesis/RiemannNormalizedCanonicalFixedProfile.lean"
    "Synthesis/RiemannNormalizedCenteredOffOscillatoryDecay.lean"
    "b3ba83902bc01414c5e7a7f6dd91330669660fc7"
    "a87c8772ada5b25450899e277da6a26536a57541"
    "a8d30e2dac912f833fb9b00d5b2a464802d6e895"

record NormalizedCenteredOffOscillatoryDecayBoundary : Set where
  constructor normalized-centered-off-oscillatory-decay-boundary
  field
    normalizedBumpArgumentsIndependentOfHeightSourceWritten : Bool
    fixedTwoWindowProfileSourceWritten : Bool
    boundedMixingCoefficientOnlyResidualShapeParameter : Bool
    fixedProfileCompactSupportSourceWritten : Bool
    normalizedPerFrequencyInverseSquareDecaySourceWritten : Bool
    literalPairIntegralTransportWithOneOverTJacobianSourceWritten : Bool

    normalizedCurvatureUniformScalarBoundPaid : Bool
    zeroWeightedNormalizedShellSummationPaid : Bool
    normalizedOffShellBelowGammaDeficitPaid : Bool

    leanKernelReceiptOwnedHere : Bool
    transportedIntoAgdaKernelHere : Bool
    h2dClosedHere : Bool
    h2eClosedHere : Bool
    r2ClosedHere : Bool
    rhDerivedHere : Bool

open NormalizedCenteredOffOscillatoryDecayBoundary public

canonicalNormalizedCenteredOffOscillatoryDecayBoundary :
  NormalizedCenteredOffOscillatoryDecayBoundary
canonicalNormalizedCenteredOffOscillatoryDecayBoundary =
  normalized-centered-off-oscillatory-decay-boundary
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
    false
    false
    false
    false
    false

normalizedPerFrequencyDecayNowSourceWritten :
  NormalizedCenteredOffOscillatoryDecayBoundary.normalizedPerFrequencyInverseSquareDecaySourceWritten
    canonicalNormalizedCenteredOffOscillatoryDecayBoundary ≡ true
normalizedPerFrequencyDecayNowSourceWritten = refl

shellSummationStillOpen :
  NormalizedCenteredOffOscillatoryDecayBoundary.zeroWeightedNormalizedShellSummationPaid
    canonicalNormalizedCenteredOffOscillatoryDecayBoundary ≡ false
shellSummationStillOpen = refl

rhStillFailClosed :
  NormalizedCenteredOffOscillatoryDecayBoundary.rhDerivedHere
    canonicalNormalizedCenteredOffOscillatoryDecayBoundary ≡ false
rhStillFailClosed = refl
