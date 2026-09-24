module DASHI.Analysis.RiemannG2NormalizedRvMHighMinCutExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Analysis.RiemannG2GammaAbsoluteMarginLeanDonorExact as Gamma
import DASHI.Analysis.RiemannG2NormalizedRvMSmoothMainDecompositionLeanDonorExact as Main
import DASHI.Analysis.RiemannG2NormalizedRvMCumulativeDiscrepancyLeanDonorExact as Remainder
import DASHI.Analysis.RiemannG2NormalizedHorizontalCorrectionLeanDonorExact as Horizontal
import DASHI.Analysis.RiemannG2NormalizedRvMAbelCompilerLeanDonorExact as Abel

------------------------------------------------------------------------
-- CURRENT NORMALIZED HIGH-SIDE MIN-CUT
--
-- The canonical high-side analysis is no longer
--
--   generic Gamma + generic Off oscillation.
--
-- It is now:
--
--   already-paid absolute Gamma margin
--     versus
--   [ smooth RvM log-shape residual
--     + theorem-bearing cumulative RvM discrepancy
--     + already-small horizontal correction ] / t.
--
-- Two former theorem-shape debts are now compiler outputs:
--
--   * the dangerous smooth log(t) mode is isolated exactly and cancels from
--     any actual q-grid carrying exact zero total test mass;
--   * a standard cumulative |N-M| bound telescopes directly into the Abel
--     prefix condition.
--
-- Therefore the remaining genuinely number-theoretic producer is allowed to
-- arrive in the ordinary cumulative RvM error form.  It need not be restated
-- as a bespoke prefix-of-increments theorem.
------------------------------------------------------------------------

record NormalizedRvMHighMinCut : Set where
  constructor normalized-rvm-high-min-cut
  field
    gammaAbsoluteMarginPaid : Bool
    horizontalCorrectionQuantitativeBoundPaid : Bool
    finiteAbelConsumerPaid : Bool

    smoothDensityConstantPlusShapePaid : Bool
    finiteZeroModeCancellationCompilerPaid : Bool
    cumulativeDiscrepancyToAbelCompilerPaid : Bool

    actualGridZeroModeTransportPaid : Bool
    residualLogShapeMainBoundPaid : Bool
    theoremBearingZetaCumulativeRvMErrorPaid : Bool
    normalizedActualCountSameObjectAttachmentPaid : Bool
    aggregateOffBelowGammaPaid : Bool

    h2AggregatePaid : Bool
    r2Paid : Bool
    rhDerivedHere : Bool

open NormalizedRvMHighMinCut public

canonicalNormalizedRvMHighMinCut : NormalizedRvMHighMinCut
canonicalNormalizedRvMHighMinCut =
  normalized-rvm-high-min-cut
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

gammaNoLongerInHighMinCut :
  NormalizedRvMHighMinCut.gammaAbsoluteMarginPaid
    canonicalNormalizedRvMHighMinCut ≡ true
gammaNoLongerInHighMinCut = refl

prefixFormNoLongerPrimitive :
  NormalizedRvMHighMinCut.cumulativeDiscrepancyToAbelCompilerPaid
    canonicalNormalizedRvMHighMinCut ≡ true
prefixFormNoLongerPrimitive = refl

actualRvMErrorStillPrimitive :
  NormalizedRvMHighMinCut.theoremBearingZetaCumulativeRvMErrorPaid
    canonicalNormalizedRvMHighMinCut ≡ false
actualRvMErrorStillPrimitive = refl

smoothResidualStillPrimitive :
  NormalizedRvMHighMinCut.residualLogShapeMainBoundPaid
    canonicalNormalizedRvMHighMinCut ≡ false
smoothResidualStillPrimitive = refl

aggregateStillFailClosed :
  NormalizedRvMHighMinCut.h2AggregatePaid
    canonicalNormalizedRvMHighMinCut ≡ false
aggregateStillFailClosed = refl
