module DASHI.Analysis.RiemannG2NormalizedZeroMeasureStieltjesLeanDonorExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- NORMALIZED ZERO-MEASURE / STIELTJES HIGH-SIDE DONOR
--
-- Companion Lean now owns the exact literal finite aggregate representation
-- needed before any Riemann--von Mangoldt subtraction.
--
-- 1. Actual reflection-paired zero atoms:
--
--      Z_rho + Z_Rrho = (1/t) A_t(rho).
--
-- 2. Exact normalized profile support gap:
--
--      H_t(v) != 0  ->  3*pi/4 < |v|,
--
--    hence H_t(v)=0 throughout |v| <= 3*pi/4.
--
-- 3. Exact horizontal split:
--
--      cosh(alpha v) = 1 + (cosh(alpha v)-1)
--
--    gives
--
--      A_t(rho)
--        = m_rho Phi_t(q_rho)
--          + m_rho E_t(alpha_rho,q_rho),
--
--    where Phi_t depends ONLY on the normalized ordinate gap q.
--
-- 4. Exact finite normalized counting functional:
--
--      <phi,mu_{t,F}>
--        = sum_{rho in F} m_rho phi(q_rho),
--
--    with monotone cumulative counting function N_{t,F}(x).
--
-- Therefore:
--
--      literal finite centered-Off aggregate
--        = (1/t) *
--            ( <Phi_t,mu_{t,F}>
--              + horizontalCorrection_t(F) ).
--
-- This is the correct one-dimensional atomic Stieltjes surface.  The remaining
-- hard analytic theorem must now:
--
--   (a) subtract a proved Riemann--von Mangoldt main-term functional from
--       <Phi_t,mu_t> before absolute values,
--   (b) bound the resulting counting-remainder pairing,
--   (c) bound the horizontal correction using |heightOf rho| <= 1/2,
--   (d) show their positive total is below the already-owned literal
--       quantitative Gamma deficit.
------------------------------------------------------------------------

record NormalizedZeroMeasureStieltjesReceipt : Set where
  constructor normalized-zero-measure-stieltjes-receipt
  field
    repository : String
    branch : String
    atomicMeasurePath : String
    spectralGapPath : String
    horizontalSplitPath : String
    stieltjesPath : String
    atomicMeasureCommit : String
    spectralGapCommit : String
    horizontalSplitCommit : String
    stieltjesCommit : String
    rootWiringCommit : String

open NormalizedZeroMeasureStieltjesReceipt public

currentNormalizedZeroMeasureStieltjesReceipt :
  NormalizedZeroMeasureStieltjesReceipt
currentNormalizedZeroMeasureStieltjesReceipt =
  normalized-zero-measure-stieltjes-receipt
    "chboishabba/dashi_lean4"
    "agent/rh-farshell-quartic-bypass"
    "Synthesis/RiemannNormalizedCenteredOffAtomicMeasure.lean"
    "Synthesis/RiemannNormalizedCenteredProfileSpectralGap.lean"
    "Synthesis/RiemannNormalizedCenteredOffHorizontalSplit.lean"
    "Synthesis/RiemannNormalizedZeroCountingStieltjes.lean"
    "1f1351a08381162a6a95df104344dd6f5f2a7caf"
    "f5bc6e8c5d1623537804adbfc05e8c4f79f50de8"
    "7ca9f0960e21b6a39e656d670899897aeb0973e7"
    "f9119efe7af2a0c4512f7f4b81b1b5a66d6c2297"
    "5786a7d7e2b55406de2a6429de34757ee5464d19"

record NormalizedZeroMeasureStieltjesBoundary : Set where
  constructor normalized-zero-measure-stieltjes-boundary
  field
    literalFiniteAtomicNormalizationSourceWritten : Bool
    normalizedProfileSpectralGapSourceWritten : Bool
    horizontalHeightSplitSourceWritten : Bool
    oneDimensionalQTransformSourceWritten : Bool
    normalizedFiniteCountingFunctionalSourceWritten : Bool
    normalizedFiniteCountMonotoneSourceWritten : Bool
    literalAggregateEqualsCountingPairPlusHorizontalSourceWritten : Bool

    rvMMainTermFunctionalImportedOrProved : Bool
    rvMMainTermSubtractionSourceWritten : Bool
    rvMCountingRemainderPairBoundPaid : Bool
    horizontalCorrectionQuantitativeBoundPaid : Bool
    aggregateOffBelowGammaDeficitPaid : Bool

    leanKernelReceiptOwnedHere : Bool
    transportedIntoAgdaKernelHere : Bool
    h2AggregateClosedHere : Bool
    r2ClosedHere : Bool
    rhDerivedHere : Bool

open NormalizedZeroMeasureStieltjesBoundary public

canonicalNormalizedZeroMeasureStieltjesBoundary :
  NormalizedZeroMeasureStieltjesBoundary
canonicalNormalizedZeroMeasureStieltjesBoundary =
  normalized-zero-measure-stieltjes-boundary
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
    false
    false

stieltjesSurfaceNowSourceWritten :
  NormalizedZeroMeasureStieltjesBoundary.literalAggregateEqualsCountingPairPlusHorizontalSourceWritten
    canonicalNormalizedZeroMeasureStieltjesBoundary ≡ true
stieltjesSurfaceNowSourceWritten = refl

rvMRemainderEstimateStillOpen :
  NormalizedZeroMeasureStieltjesBoundary.rvMCountingRemainderPairBoundPaid
    canonicalNormalizedZeroMeasureStieltjesBoundary ≡ false
rvMRemainderEstimateStillOpen = refl

aggregateH2StillFailClosed :
  NormalizedZeroMeasureStieltjesBoundary.h2AggregateClosedHere
    canonicalNormalizedZeroMeasureStieltjesBoundary ≡ false
aggregateH2StillFailClosed = refl
