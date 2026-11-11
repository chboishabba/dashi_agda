module DASHI.Physics.YangMills.YMClayE1D1CrossNumeratorCenteringAlgebraExact where

------------------------------------------------------------------------
-- P0.01--P0.04: the ACTUAL original Wilson bare center source.
--
-- Existing RealAnalysisAxioms treats subtraction, unary minus, and
-- division as separate postulated operations and does NOT give their
-- usual mutual field laws. We therefore expose the exact scalar
-- compatibility laws as ARGUMENTS, not new postulates or physical
-- Wilson assumptions. An implementation of the selected real field
-- must supply these before claiming unconditional P0.01 / P0.03.
--
-- All numerator identities here use the actual original side-two
-- Wilson Gibbs/Haar finite measure and source linearity. No auxiliary
-- expectation is introduced, and no function extensionality is used.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)
open import DASHI.Foundations.RealAnalysisAxioms using
  (ℝ; 0ℝ; 1ℝ; _+ℝ_; _-ℝ_; _*ℝ_; -ℝ_; _<ℝ_; _≤ℝ_)

import DASHI.Physics.YangMills.SUNMatrixCarrier as SUN
import DASHI.Physics.YangMills.YMClaySUNMatrixWilsonTraceGaugeExact as Trace
import DASHI.Physics.YangMills.YMClayFiniteProductHaarPermutationExact as Haar
import DASHI.Physics.YangMills.YMClayFiniteProductHaarOrderedAlgebraExact as Ordered
import DASHI.Physics.YangMills.YMClaySUNProductHaarGaugeFromOneLinkExact as Bilateral
import DASHI.Physics.Foundations.CMP119AntigravityRealGibbsDensityPositiveExact as Exp
import DASHI.Physics.YangMills.YMClayE1D1CrossNumeratorCenteringExact as Center
import DASHI.Physics.YangMills.YMClayOriginalWilsonFiniteNumeratorOrderExact as Numerator
import DASHI.Physics.YangMills.YMClayOriginalWilsonFiniteTwoSourceJetExact as Original
import DASHI.Physics.YangMills.YangMillsClayPinnedPhysicalCarriersExact as Physical

-- P0.01 is a real-carrier compatibility requirement, NOT derivable
-- solely from the currently independent RealAnalysisAxioms operations.
record OriginalRealCenteringLaws : Set where
  field
    subtractionAsNegation :
      (x c : ℝ) →
      x -ℝ c ≡ x +ℝ (-ℝ c) *ℝ 1ℝ

    centeredCancellation :
      (numerator value partition : ℝ) →
      numerator ≡ value *ℝ partition →
      numerator +ℝ (-ℝ value) *ℝ partition ≡ 0ℝ

open OriginalRealCenteringLaws public

-- Explicit selected nonzero-denominator quotient reconstruction.
-- The positive partition comes from the ORIGINAL Wilson measure.
record OriginalRealPositiveDivisionLaws
    (divide : ℝ → ℝ → ℝ) : Set where
  field
    quotientTimesPositiveDenominator :
      (numerator denominator : ℝ) →
      0ℝ <ℝ denominator →
      divide numerator denominator *ℝ denominator ≡ numerator

open OriginalRealPositiveDivisionLaws public

module _
    {Matrix Complex : Set} {N : Nat}
    (theory : SUN.CertifiedSUNMatrixTheory N Matrix Complex)
    (traceData : Trace.SUNMatrixRealTrace {Scalar = ℝ} theory)
    (exponential : Exp.StrictPositiveRealExponential)
    (beta : Nat → ℝ)
    (oneLink : Haar.OneLinkProductHaar (SUN.SUNMatrixElement theory))
    (bilateral : Bilateral.OneLinkSUNBilateralHaar theory oneLink)
    (divide : ℝ → ℝ → ℝ)
    (ordered : Ordered.OneLinkOrderedHaarAlgebra oneLink)
    (strictToWeak : ∀ {value} → 0ℝ <ℝ value → 0ℝ ≤ℝ value)
    (strict : Ordered.OneLinkStrictlyPositiveIntegration oneLink)
    (realLaws : OriginalRealCenteringLaws)
    (divisionLaws : OriginalRealPositiveDivisionLaws divide)
  where

  CoarseTest : Set
  CoarseTest =
    Center.CoarseTest
      theory traceData exponential beta oneLink bilateral divide
      ordered strictToWeak

  bareNumerator : CoarseTest → ℝ
  bareNumerator =
    Center.bareNumerator
      theory traceData exponential beta oneLink bilateral divide
      ordered strictToWeak

  bareExpectation : CoarseTest → ℝ
  bareExpectation =
    Original.originalWilsonExpectation
      theory traceData exponential beta oneLink bilateral divide 1

  barePartition : ℝ
  barePartition =
    Center.zBare
      theory traceData exponential beta oneLink bilateral divide
      ordered strictToWeak

  -- P0.01 / P0.02: closed once selected scalar carrier laws are
  -- supplied; this consumes the ALREADY proved source centering.
  originalRealSubtractionAsAddition :
    (x c : ℝ) →
    x -ℝ c ≡ x +ℝ (-ℝ c) *ℝ 1ℝ
  originalRealSubtractionAsAddition =
    subtractionAsNegation realLaws

  originalWilsonCrossNumeratorSubtractionCenteringClosed :
    (F : CoarseTest) (c : ℝ) →
    Center.X theory traceData exponential beta oneLink bilateral divide
      ordered strictToWeak (λ U → F U -ℝ c)
    ≡
    Center.X theory traceData exponential beta oneLink bilateral divide
      ordered strictToWeak F
  originalWilsonCrossNumeratorSubtractionCenteringClosed F c =
    Center.originalWilsonCrossNumeratorSubtractionCentering
      theory traceData exponential beta oneLink bilateral divide
      ordered strictToWeak F c
      (λ value → subtractionAsNegation realLaws value c)

  -- P0.03: using the ACTUAL original bare Wilson partition (n = 1),
  -- and no independent normalization or denominator oracle.
  originalBareExpectationMultiplyPartition :
    (F : CoarseTest) →
    bareExpectation F *ℝ barePartition ≡ bareNumerator F
  originalBareExpectationMultiplyPartition F =
    quotientTimesPositiveDenominator divisionLaws
      (bareNumerator F) barePartition
      (Numerator.originalWilsonPartitionStrictlyPositive
        theory traceData exponential beta oneLink bilateral divide
        ordered strictToWeak strict 1)

  -- P0.04 for literal subtraction. First the already source-written
  -- bare numerator shift is used, then real additive cancellation.
  originalBareCenteredNumeratorZero :
    (F : CoarseTest) →
    bareNumerator (λ U → F U -ℝ bareExpectation F) ≡ 0ℝ
  originalBareCenteredNumeratorZero F =
    trans
      (Center.bareNumeratorCongruent
        theory traceData exponential beta oneLink bilateral divide
        ordered strictToWeak
        (λ U → F U -ℝ bareExpectation F)
        (Center.shiftByConstant
          theory traceData exponential beta oneLink bilateral divide
          ordered strictToWeak F (-ℝ bareExpectation F))
        (λ U → subtractionAsNegation realLaws
          (F U) (bareExpectation F)))
      (trans
        (Center.bareShiftNumerator
          theory traceData exponential beta oneLink bilateral divide
          ordered strictToWeak
          F (-ℝ bareExpectation F))
        (centeredCancellation realLaws
          (bareNumerator F) (bareExpectation F) barePartition
          (sym (originalBareExpectationMultiplyPartition F))))
