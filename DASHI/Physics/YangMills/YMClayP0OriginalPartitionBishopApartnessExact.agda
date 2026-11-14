module DASHI.Physics.YangMills.YMClayP0OriginalPartitionBishopApartnessExact where

------------------------------------------------------------------------
-- ORIGINAL WILSON FINITE PARTITION -> CONSTRUCTED BISHOP APARTNESS.
--
-- Source: literal finite Wilson Gibbs/Haar strict partition positivity in
-- YMClayOriginalWilsonFiniteNumeratorOrderExact (same original measure).
-- Constructive source: Murray/Csimma Bishop reals and their apartness
-- inverse in YMClayP0BishopRealCarrierInstancesExact.
--
-- The OriginalWilsonToBishopScalarWeld W remains UNINHABITED in this
-- independently postulated RealAnalysisAxioms.ℝ source. The results
-- are genuinely conditional on W, not a claim of field interpretation.
-- No new postulate, physical RG estimate, or continuum mass gap.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Equality using (_≡_)

import DASHI.Foundations.RealAnalysisAxioms as R
import Real as B
import Inverse as Inv

import DASHI.Physics.YangMills.SUNMatrixCarrier as SUN
import DASHI.Physics.YangMills.YMClaySUNMatrixWilsonTraceGaugeExact as Trace
import DASHI.Physics.YangMills.YMClayFiniteProductHaarPermutationExact as Haar
import DASHI.Physics.YangMills.YMClayFiniteProductHaarOrderedAlgebraExact as Ordered
import DASHI.Physics.YangMills.YMClaySUNProductHaarGaugeFromOneLinkExact as Bilateral
import DASHI.Physics.Foundations.CMP119AntigravityRealGibbsDensityPositiveExact as Exp
import DASHI.Physics.YangMills.YMClayOriginalWilsonFiniteNumeratorOrderExact as Order
import DASHI.Physics.YangMills.YangMillsClayPinnedPhysicalCarriersExact as Physical
import DASHI.Physics.YangMills.YMClayP0BishopRealCarrierInstancesExact as BishopP0
import DASHI.Physics.YangMills.YMClayP0BishopToOriginalWilsonRealWeldExact as Weld

module _
    {Matrix Complex : Set} {N : Nat}
    (theory : SUN.CertifiedSUNMatrixTheory N Matrix Complex)
    (traceData : Trace.SUNMatrixRealTrace {Scalar = R.ℝ} theory)
    (exponential : Exp.StrictPositiveRealExponential)
    (beta : Nat → R.ℝ)
    (oneLink : Haar.OneLinkProductHaar (SUN.SUNMatrixElement theory))
    (bilateral : Bilateral.OneLinkSUNBilateralHaar theory oneLink)
    (divide : R.ℝ → R.ℝ → R.ℝ)
    (ordered : Ordered.OneLinkOrderedHaarAlgebra oneLink)
    (strictToWeak : ∀ {x} →
      R._<ℝ_ R.0ℝ x → R._≤ℝ_ R.0ℝ x)
    (strict : Ordered.OneLinkStrictlyPositiveIntegration oneLink)
    (W : Weld.OriginalWilsonToBishopScalarWeld divide)
  where

  originalPartition : Nat → R.ℝ
  originalPartition n =
    Physical.partitionFunction
      (Order.wilsonMeasure
        theory traceData exponential beta oneLink bilateral divide
        ordered strictToWeak n)

  originalPartitionPositive : (n : Nat) →
    R._<ℝ_ R.0ℝ (originalPartition n)
  originalPartitionPositive n =
    Order.originalWilsonPartitionStrictlyPositive
      theory traceData exponential beta oneLink bilateral divide
      ordered strictToWeak strict n

  -- Source positivity is preserved by W; W is not manufactured.
  partitionImagePositive : (n : Nat) →
    B._<_ B.0ℝ (Weld.map W (originalPartition n))
  partitionImagePositive n =
    Weld.preservePositive W (originalPartitionPositive n)

  -- The original partition (on the same Wilson Gibbs/Haar source)
  -- has precisely the Bishop apartness required by its inverse.
  partitionImageApartZero : (n : Nat) →
    Weld.map W (originalPartition n) B.≄0
  partitionImageApartZero n =
    BishopP0.bishopPositiveDenominatorApartFromZero
      (Weld.map W (originalPartition n))
      (partitionImagePositive n)

  selectedBishopPartitionInverse : Nat → B.ℝ
  selectedBishopPartitionInverse n =
    Inv._⁻¹
      (Weld.map W (originalPartition n))
      (partitionImageApartZero n)

  partitionImageQuotientCancellation :
    (n : Nat) (numerator : R.ℝ) →
    B._≃_
      (B._*_
        (B._*_
          (Weld.map W numerator)
          (selectedBishopPartitionInverse n))
        (Weld.map W (originalPartition n)))
      (Weld.map W numerator)
  partitionImageQuotientCancellation n numerator =
    BishopP0.bishopPositiveQuotientTimesDenominator
      (Weld.map W numerator)
      (Weld.map W (originalPartition n))
      (partitionImagePositive n)

  -- SAME selected Wilson divide, not an unrelated quotient.
  originalWilsonPositiveDivideCancellation :
    (n : Nat) (numerator : R.ℝ) →
    R._*ℝ_ (divide numerator (originalPartition n))
      (originalPartition n) ≡ numerator
  originalWilsonPositiveDivideCancellation n numerator =
    Weld.weldDerivesOriginalPositiveDivision W
      numerator (originalPartition n)
      (originalPartitionPositive n)
