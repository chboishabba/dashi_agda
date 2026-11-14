module DASHI.Physics.YangMills.YMClayOriginalWilsonFiniteNumeratorOrderExact where

------------------------------------------------------------------------
-- Genuine original Wilson finite weighted numerator order.
--
-- The physical measure here is precisely the selected n-dependent
-- original SU(N) Wilson Gibbs/Haar measure from the original R445
-- source, with its actual beta(n), link fields, six-plane Wilson action,
-- partition and product Haar integral.
--
-- Unlike an abstract positivity record, every result below constructs
-- its integration laws from originalWilsonFiniteIntegrationLaws.
--
-- A pointwise nonnegative original test has nonnegative numerator.
-- If an original test has an explicit nonnegative slack to the unit
-- observable, its numerator is bounded by the SAME original partition.
--
-- No normalized quotient monotonicity, constant trace bound, cutoff-
-- uniform RG error, continuum convergence or OS gap is asserted.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary.PropositionalEquality using
  (cong; sym; trans; subst)
open import DASHI.Foundations.RealAnalysisAxioms using
  (ℝ; 0ℝ; 1ℝ; _+ℝ_; _*ℝ_; _<ℝ_; _≤ℝ_;
   ≤ℝ-refl; +-mono-≤; +-identityʳ)

import DASHI.Physics.YangMills.SUNMatrixCarrier as SUN
import DASHI.Physics.YangMills.YMClaySUNMatrixWilsonTraceGaugeExact as Trace
import DASHI.Physics.YangMills.YMClayFiniteProductHaarPermutationExact as Haar
import DASHI.Physics.YangMills.YMClayFiniteProductHaarOrderedAlgebraExact as Ordered
import DASHI.Physics.YangMills.YMClaySUNProductHaarGaugeFromOneLinkExact as Bilateral
import DASHI.Physics.Foundations.CMP119AntigravityRealGibbsDensityPositiveExact as Exp
import DASHI.Physics.YangMills.YMClayOriginalWilsonFiniteTwoSourceJetExact as Original
import DASHI.Physics.YangMills.YMClaySUNVariablePhysicalCutoffFamilyExact as Family
import DASHI.Physics.YangMills.YangMillsClayPinnedPhysicalCarriersExact as Physical
import DASHI.Physics.YangMills.YangMillsPhysicalFiniteMeasureCylinderAlgebraExact as Finite

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
  where

  WilsonTest : Nat → Set
  WilsonTest =
    Original.OriginalObservable
      theory traceData exponential beta oneLink bilateral divide

  wilsonMeasure :
    (n : Nat) →
    Physical.PhysicalFiniteYMMeasure (Original.OriginalLinks
      theory traceData exponential beta oneLink bilateral divide n) ℝ
  wilsonMeasure =
    Original.originalWilsonMeasure
      theory traceData exponential beta oneLink bilateral divide

  wilsonNumerator : (n : Nat) → WilsonTest n → ℝ
  wilsonNumerator n =
    Finite.unnormalizedNumerator (wilsonMeasure n)

  sourceIntegration :
    (n : Nat) →
    Finite.PhysicalFiniteMeasureIntegrationLaws (wilsonMeasure n)
  sourceIntegration n =
    Original.originalWilsonFiniteIntegrationLaws
      theory traceData exponential beta oneLink bilateral divide
      ordered strictToWeak n

  originalWilsonNumeratorCongruent :
    (n : Nat) (left right : WilsonTest n) →
    (∀ links → left links ≡ right links) →
    wilsonNumerator n left ≡ wilsonNumerator n right
  originalWilsonNumeratorCongruent n left right equal =
    Finite.haarIntegralCongruent
      (sourceIntegration n)
      (λ links → Physical.density (wilsonMeasure n) links *ℝ left links)
      (λ links → Physical.density (wilsonMeasure n) links *ℝ right links)
      (λ links → cong
        (λ value → Physical.density (wilsonMeasure n) links *ℝ value)
        (equal links))

  originalWilsonNumeratorPositive :
    (n : Nat) (test : WilsonTest n) →
    (∀ links → 0ℝ ≤ℝ test links) →
    0ℝ ≤ℝ wilsonNumerator n test
  originalWilsonNumeratorPositive n test nonnegative =
    Finite.numeratorPositive (sourceIntegration n) test nonnegative

  originalWilsonNumeratorAdd :
    (n : Nat) (left right : WilsonTest n) →
    wilsonNumerator n (λ links → left links +ℝ right links)
    ≡ wilsonNumerator n left +ℝ wilsonNumerator n right
  originalWilsonNumeratorAdd n left right =
    Finite.numeratorAdd (sourceIntegration n) left right

  -- Actual source-numerator monotonicity from a certified pointwise
  -- nonnegative slack. This avoids silently assuming arbitrary real
  -- subtraction-order laws or monotonicity of a new Haar functional.
  originalWilsonNumeratorMonotoneFromSlack :
    (n : Nat) (lower upper slack : WilsonTest n) →
    (∀ links → 0ℝ ≤ℝ slack links) →
    (∀ links → lower links +ℝ slack links ≡ upper links) →
    wilsonNumerator n lower ≤ℝ wilsonNumerator n upper
  originalWilsonNumeratorMonotoneFromSlack
    n lower upper slack nonnegative pointwise =
    let
      lowerNum = wilsonNumerator n lower
      slackNum = wilsonNumerator n slack

      slackNumNonnegative : 0ℝ ≤ℝ slackNum
      slackNumNonnegative =
        originalWilsonNumeratorPositive n slack nonnegative

      lowerBelowSum : lowerNum ≤ℝ lowerNum +ℝ slackNum
      lowerBelowSum =
        subst
          (λ value → value ≤ℝ lowerNum +ℝ slackNum)
          (+-identityʳ lowerNum)
          (+-mono-≤ ≤ℝ-refl slackNumNonnegative)

      sumIsUpper :
        lowerNum +ℝ slackNum ≡ wilsonNumerator n upper
      sumIsUpper =
        trans
          (sym (originalWilsonNumeratorAdd n lower slack))
          (originalWilsonNumeratorCongruent n
            (λ links → lower links +ℝ slack links)
            upper pointwise)
    in
    subst (λ value → lowerNum ≤ℝ value) sumIsUpper lowerBelowSum

  -- This upper bound is at the ORIGINAL physical partition, not a
  -- synthetic constant bound on a separately selected functional.
  originalWilsonNumeratorBelowItsPartition :
    (n : Nat) (test complement : WilsonTest n) →
    (∀ links → 0ℝ ≤ℝ complement links) →
    (∀ links → test links +ℝ complement links ≡ 1ℝ) →
    wilsonNumerator n test
      ≤ℝ Physical.partitionFunction (wilsonMeasure n)
  originalWilsonNumeratorBelowItsPartition
    n test complement complementNonnegative completesOne =
    subst
      (λ value → wilsonNumerator n test ≤ℝ value)
      (Original.originalWilsonUnitNumeratorIsPartition
        theory traceData exponential beta oneLink bilateral divide
        ordered strictToWeak n)
      (originalWilsonNumeratorMonotoneFromSlack
        n test (λ _ → 1ℝ) complement
        complementNonnegative completesOne)

  ----------------------------------------------------------------------
  -- Normalized original Wilson order, using ONLY the selected original
  -- positive partition and standard ordered-real division lemmas.
  -- No independent normalized probability source is introduced.
  ----------------------------------------------------------------------

  originalWilsonPartitionStrictlyPositive :
    (strict : Ordered.OneLinkStrictlyPositiveIntegration oneLink)
    (n : Nat) →
    0ℝ <ℝ Physical.partitionFunction (wilsonMeasure n)
  originalWilsonPartitionStrictlyPositive strict n =
    Family.physicalFinitePartitionPositive
      theory traceData exponential beta oneLink bilateral divide
      strict n

  originalWilsonNormalizedBelowOne :
    (strict : Ordered.OneLinkStrictlyPositiveIntegration oneLink)
    (divideOrder :
      ∀ {a b denominator : ℝ} →
      0ℝ <ℝ denominator →
      a ≤ℝ b →
      divide a denominator ≤ℝ divide b denominator)
    (divideSelf :
      ∀ denominator →
      0ℝ <ℝ denominator → divide denominator denominator ≡ 1ℝ)
    (n : Nat) (test complement : WilsonTest n) →
    (∀ links → 0ℝ ≤ℝ complement links) →
    (∀ links → test links +ℝ complement links ≡ 1ℝ) →
    Physical.normalizedExpectation (wilsonMeasure n) test ≤ℝ 1ℝ
  originalWilsonNormalizedBelowOne
    strict divideOrder divideSelf n test complement
    complementNonnegative completesOne =
    subst
      (λ upper →
        Physical.normalizedExpectation (wilsonMeasure n) test ≤ℝ upper)
      (divideSelf
        (Physical.partitionFunction (wilsonMeasure n))
        (originalWilsonPartitionStrictlyPositive strict n))
      (divideOrder
        (originalWilsonPartitionStrictlyPositive strict n)
        (originalWilsonNumeratorBelowItsPartition
          n test complement complementNonnegative completesOne))

  originalWilsonNormalizedNonnegative :
    (strict : Ordered.OneLinkStrictlyPositiveIntegration oneLink)
    (divideOrder :
      ∀ {a b denominator : ℝ} →
      0ℝ <ℝ denominator →
      a ≤ℝ b →
      divide a denominator ≤ℝ divide b denominator)
    (divideZero :
      ∀ denominator →
      0ℝ <ℝ denominator → divide 0ℝ denominator ≡ 0ℝ)
    (n : Nat) (test : WilsonTest n) →
    (∀ links → 0ℝ ≤ℝ test links) →
    0ℝ ≤ℝ Physical.normalizedExpectation (wilsonMeasure n) test
  originalWilsonNormalizedNonnegative
    strict divideOrder divideZero n test testNonnegative =
    subst
      (λ lower →
        lower ≤ℝ Physical.normalizedExpectation (wilsonMeasure n) test)
      (divideZero
        (Physical.partitionFunction (wilsonMeasure n))
        (originalWilsonPartitionStrictlyPositive strict n))
      (divideOrder
        (originalWilsonPartitionStrictlyPositive strict n)
        (originalWilsonNumeratorPositive n test testNonnegative))
