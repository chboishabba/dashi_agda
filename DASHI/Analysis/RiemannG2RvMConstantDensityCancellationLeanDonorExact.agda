module DASHI.Analysis.RiemannG2RvMConstantDensityCancellationLeanDonorExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- EXACT CONSTANT-DENSITY RvM CANCELLATION
--
-- Companion Lean restores the canonical bump's full C-infinity regularity,
-- realizes the normalized centered complex profile as a Schwartz function,
-- and welds Mathlib's Fourier transform back to the literal normalized Off
-- cosine transform:
--
--   Fourier(4 H_t)(w) = Phi_t(2*pi*w).
--
-- The normalized centered profile has an open zero-mode gap and in particular
--
--   H_t(0) = 0.
--
-- Fourier inversion at zero plus exact Haar scaling therefore gives
--
--   integral_R Phi_t(q) dq = 0.
--
-- Consequently every q-constant smooth spectral density pairs to exactly zero:
--
--   integral_R c * Phi_t(q) dq = 0.
--
-- This pays the dangerous constant/log(t) component of the smooth
-- Riemann--von Mangoldt density before any absolute value.
--
-- It does NOT yet pay:
--
--   * the q-dependent smooth main-density residual (for example the
--     log(1+q)-type term after local normalization),
--   * a theorem-bearing actual-minus-main cumulative zero-count remainder,
--   * the final aggregate Off < Gamma comparison.
------------------------------------------------------------------------

record RvMConstantDensityCancellationReceipt : Set where
  constructor rvm-constant-density-cancellation-receipt
  field
    repository : String
    branch : String
    zeroModePath : String
    schwartzPath : String
    fourierCosineWeldPath : String
    constantCancellationPath : String
    zeroModeCommit : String
    schwartzCommit : String
    fourierCosineWeldCommit : String
    constantCancellationCommit : String
    rootWiringCommit : String

open RvMConstantDensityCancellationReceipt public

currentRvMConstantDensityCancellationReceipt :
  RvMConstantDensityCancellationReceipt
currentRvMConstantDensityCancellationReceipt =
  rvm-constant-density-cancellation-receipt
    "chboishabba/dashi_lean4"
    "agent/rh-farshell-quartic-bypass"
    "Synthesis/RiemannNormalizedRvMZeroModeFourier.lean"
    "Synthesis/RiemannNormalizedCenteredProfileSchwartz.lean"
    "Synthesis/RiemannNormalizedRvMFourierCosineWeld.lean"
    "Synthesis/RiemannNormalizedRvMConstantDensityCancellation.lean"
    "eb132ae0ab5f5e192fe81e596363d8d8495548cb"
    "b25ad8cf4dfabd656e2acdcdf29ed8b9aa6f832e"
    "1235fd265816033591b67455e22d2ba693216a3f"
    "b00e1be7e9c8e408b0e1fc24a519f077bef28778"
    "b6a8a2cbdf90fc488a742c311b8c8ef8663ac1eb"

record RvMConstantDensityCancellationBoundary : Set where
  constructor rvm-constant-density-cancellation-boundary
  field
    normalizedProfileCinfinitySourceWritten : Bool
    normalizedProfileSchwartzSourceWritten : Bool
    specificFourierL1SourceWritten : Bool
    fourierEqualsLiteralCosineTransformSourceWritten : Bool
    literalBaseTransformIntegrableSourceWritten : Bool
    literalBaseTransformIntegralZeroSourceWritten : Bool
    constantDensityPairZeroSourceWritten : Bool

    qDependentSmoothMainResidualPaid : Bool
    cumulativeActualMinusMainRemainderPaid : Bool
    aggregateOffBelowGammaPaid : Bool

    leanKernelReceiptOwnedHere : Bool
    transportedIntoAgdaKernelHere : Bool
    h2AggregateClosedHere : Bool
    r2ClosedHere : Bool
    rhDerivedHere : Bool

open RvMConstantDensityCancellationBoundary public

canonicalRvMConstantDensityCancellationBoundary :
  RvMConstantDensityCancellationBoundary
canonicalRvMConstantDensityCancellationBoundary =
  rvm-constant-density-cancellation-boundary
    true
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

constantSpectralDensityNowKilledExactly :
  RvMConstantDensityCancellationBoundary.constantDensityPairZeroSourceWritten
    canonicalRvMConstantDensityCancellationBoundary ≡ true
constantSpectralDensityNowKilledExactly = refl

smoothMainResidualStillOpen :
  RvMConstantDensityCancellationBoundary.qDependentSmoothMainResidualPaid
    canonicalRvMConstantDensityCancellationBoundary ≡ false
smoothMainResidualStillOpen = refl

rvMRemainderStillOpen :
  RvMConstantDensityCancellationBoundary.cumulativeActualMinusMainRemainderPaid
    canonicalRvMConstantDensityCancellationBoundary ≡ false
rvMRemainderStillOpen = refl
