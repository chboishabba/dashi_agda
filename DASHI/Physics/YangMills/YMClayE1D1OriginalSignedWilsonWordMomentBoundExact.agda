module DASHI.Physics.YangMills.YMClayE1D1OriginalSignedWilsonWordMomentBoundExact where

------------------------------------------------------------------------
-- P0.06: SIGNED original Wilson words on the ACTUAL finite SU(N)
-- Gibbs/Haar source, at EVERY original cutoff.
--
-- A normalized real Wilson trace (and its word products) generally
-- lies in [-1,1], NOT [0,1].  So the earlier nonnegative-complement
-- theorem does not directly bound its expectation.
--
-- Here the ordinary scalar real order/negation laws and the concrete
-- matrix trace range are named precisely. Given those, both
-- 1 - W and 1 + W are pointwise nonnegative; the original
-- product-Haar numerator order proves
--       N_n(W) <= Z_n   and   N_n(-W) <= Z_n,
-- hence |N_n(W)| <= Z_n, then |E_n(W)| <= 1 by the
-- selected positive denominator's absolute quotient order.
--
-- No NEW postulate or independent Wilson measure.  This does NOT
-- construct the arbitrary SU(N) matrix trace norm nor the real
-- scalar compatibility laws: those remain distinct source debts.
-- No physical RG contraction, E1 continuum or OS gap is inferred.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary.PropositionalEquality using (sym; trans; subst)
open import DASHI.Foundations.RealAnalysisAxioms using
  (ℝ; 0ℝ; 1ℝ; _+ℝ_; _-ℝ_; _*ℝ_; -ℝ_; _≤ℝ_; _<ℝ_; absℝ)

import DASHI.Physics.YangMills.SUNMatrixCarrier as SUN
import DASHI.Physics.YangMills.YMClaySUNMatrixWilsonTraceGaugeExact as Trace
import DASHI.Physics.YangMills.YMClayFiniteProductHaarPermutationExact as Haar
import DASHI.Physics.YangMills.YMClayFiniteProductHaarOrderedAlgebraExact as Ordered
import DASHI.Physics.YangMills.YMClaySUNProductHaarGaugeFromOneLinkExact as Bilateral
import DASHI.Physics.Foundations.CMP119AntigravityRealGibbsDensityPositiveExact as Exp
import DASHI.Physics.YangMills.YMClayE1D1OriginalVariablePlaquetteWordsExact as Words
import DASHI.Physics.YangMills.YMClaySUNSideFourBlockedPushforwardCylinderAlgebraExact as Push
import DASHI.Physics.YangMills.YMClayE1D1OriginalSUNTraceToAllWordsBoundExact as WordBound
import DASHI.Physics.YangMills.YMClayOriginalWilsonFiniteNumeratorOrderExact as OriginalOrder
import DASHI.Physics.YangMills.YangMillsPhysicalFiniteMeasureCylinderAlgebraExact as Finite
import DASHI.Physics.YangMills.YangMillsClayPinnedPhysicalCarriersExact as Physical

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
    (strictToWeak : ∀ {x} → 0ℝ <ℝ x → 0ℝ ≤ℝ x)
    (strict : Ordered.OneLinkStrictlyPositiveIntegration oneLink)

    -- Genuine same-carrier matrix SU(N) trace range, not cyclicity.
    (matrixTraceRange : ∀ U →
      absℝ (Trace.matrixWilsonValue traceData U) ≤ℝ 1ℝ)
    (absNonnegative : ∀ x → 0ℝ ≤ℝ absℝ x)
    (absOne : absℝ 1ℝ ≡ 1ℝ)

    -- Only selected REAL arithmetic/order compatibility, independent
    -- of all physical Wilson/renormalisation dynamics.
    (oneMinusNN : ∀ x → absℝ x ≤ℝ 1ℝ →
      0ℝ ≤ℝ (1ℝ -ℝ x))
    (onePlusNN : ∀ x → absℝ x ≤ℝ 1ℝ →
      0ℝ ≤ℝ (1ℝ +ℝ x))
    (oneMinusCompletes : ∀ x →
      x +ℝ (1ℝ -ℝ x) ≡ 1ℝ)
    (onePlusCompletes : ∀ x →
      (-ℝ x) +ℝ (1ℝ +ℝ x) ≡ 1ℝ)
    (negAsScale : ∀ x →
      -ℝ x ≡ (-ℝ 1ℝ) *ℝ x)
    (absFromSignedBounds : ∀ x upper →
      x ≤ℝ upper → (-ℝ x) ≤ℝ upper →
      absℝ x ≤ℝ upper)
    (divideSignedUnitBound : ∀ x z →
      0ℝ <ℝ z →
      absℝ x ≤ℝ z →
      absℝ (divide x z) ≤ℝ 1ℝ)
  where

  OriginalWord : Nat → Set
  OriginalWord n =
    Words.PlaquetteWord
      theory traceData exponential beta oneLink bilateral divide n

  originalWordTest :
    (n : Nat) → OriginalWord n →
    OriginalOrder.WilsonTest
      theory traceData exponential beta oneLink bilateral divide
      ordered strictToWeak n
  originalWordTest n =
    Words.originalWordObservable
      theory traceData exponential beta oneLink bilateral divide n

  numerator : (n : Nat) →
    OriginalOrder.WilsonTest
      theory traceData exponential beta oneLink bilateral divide
      ordered strictToWeak n → ℝ
  numerator =
    OriginalOrder.wilsonNumerator
      theory traceData exponential beta oneLink bilateral divide
      ordered strictToWeak

  partition : Nat → ℝ
  partition n =
    Physical.partitionFunction
      (OriginalOrder.wilsonMeasure
        theory traceData exponential beta oneLink bilateral divide
        ordered strictToWeak n)

  originalWordAbsBelowOne :
    (n : Nat) (w : OriginalWord n) →
    ∀ links → absℝ (originalWordTest n w links) ≤ℝ 1ℝ
  originalWordAbsBelowOne n w links =
    WordBound.originalAllLengthWilsonWordMagnitudeBound
      theory traceData exponential beta oneLink bilateral divide
      matrixTraceRange absNonnegative absOne n w links

  originalWordNumeratorUpper :
    (n : Nat) (w : OriginalWord n) →
    numerator n (originalWordTest n w) ≤ℝ partition n
  originalWordNumeratorUpper n w =
    OriginalOrder.originalWilsonNumeratorBelowItsPartition
      theory traceData exponential beta oneLink bilateral divide
      ordered strictToWeak
      n (originalWordTest n w)
      (λ links → 1ℝ -ℝ originalWordTest n w links)
      (λ links → oneMinusNN
        (originalWordTest n w links) (originalWordAbsBelowOne n w links))
      (λ links → oneMinusCompletes (originalWordTest n w links))

  originalNegWordNumeratorUpper :
    (n : Nat) (w : OriginalWord n) →
    numerator n (λ links → -ℝ originalWordTest n w links)
      ≤ℝ partition n
  originalNegWordNumeratorUpper n w =
    OriginalOrder.originalWilsonNumeratorBelowItsPartition
      theory traceData exponential beta oneLink bilateral divide
      ordered strictToWeak n
      (λ links → -ℝ originalWordTest n w links)
      (λ links → 1ℝ +ℝ originalWordTest n w links)
      (λ links → onePlusNN
        (originalWordTest n w links) (originalWordAbsBelowOne n w links))
      (λ links → onePlusCompletes (originalWordTest n w links))

  originalNegWordNumeratorIsNegation :
    (n : Nat) (w : OriginalWord n) →
    numerator n (λ links → -ℝ originalWordTest n w links)
    ≡ -ℝ (numerator n (originalWordTest n w))
  originalNegWordNumeratorIsNegation n w =
    trans
      (OriginalOrder.originalWilsonNumeratorCongruent
        theory traceData exponential beta oneLink bilateral divide
        ordered strictToWeak n
        (λ links → -ℝ originalWordTest n w links)
        (λ links → (-ℝ 1ℝ) *ℝ originalWordTest n w links)
        (λ links → negAsScale (originalWordTest n w links)))
      (trans
        (Finite.numeratorScale
          (OriginalOrder.sourceIntegration
            theory traceData exponential beta oneLink bilateral divide
            ordered strictToWeak n)
          (-ℝ 1ℝ) (originalWordTest n w))
        (sym (negAsScale
          (numerator n (originalWordTest n w)))))

  originalWordNumeratorAbsoluteBelowPartition :
    (n : Nat) (w : OriginalWord n) →
    absℝ (numerator n (originalWordTest n w)) ≤ℝ partition n
  originalWordNumeratorAbsoluteBelowPartition n w =
    absFromSignedBounds
      (numerator n (originalWordTest n w))
      (partition n)
      (originalWordNumeratorUpper n w)
      (subst
        (λ value → value ≤ℝ partition n)
        (originalNegWordNumeratorIsNegation n w)
        (originalNegWordNumeratorUpper n w))

  originalWordNormalizedAbsoluteBelowOne :
    (n : Nat) (w : OriginalWord n) →
    absℝ
      (Physical.normalizedExpectation
        (OriginalOrder.wilsonMeasure
          theory traceData exponential beta oneLink bilateral divide
          ordered strictToWeak n)
        (originalWordTest n w))
      ≤ℝ 1ℝ
  originalWordNormalizedAbsoluteBelowOne n w =
    divideSignedUnitBound
      (numerator n (originalWordTest n w)) (partition n)
      (OriginalOrder.originalWilsonPartitionStrictlyPositive
        theory traceData exponential beta oneLink bilateral divide
        ordered strictToWeak strict n)
      (originalWordNumeratorAbsoluteBelowPartition n w)

  ----------------------------------------------------------------------
  -- The stronger original-PHYSICAL result is formulated for any
  -- certified signed bounded source test (not only Wilson words).
  -- This permits the actual R445 fine n=3 native-block pullback of
  -- an independently chosen n=1 coarse Wilson word.
  ----------------------------------------------------------------------

  originalBoundedTestNumeratorUpper :
    (n : Nat)
    (test : OriginalOrder.WilsonTest
      theory traceData exponential beta oneLink bilateral divide
      ordered strictToWeak n) →
    (∀ links → absℝ (test links) ≤ℝ 1ℝ) →
    numerator n test ≤ℝ partition n
  originalBoundedTestNumeratorUpper n test bounded =
    OriginalOrder.originalWilsonNumeratorBelowItsPartition
      theory traceData exponential beta oneLink bilateral divide
      ordered strictToWeak n
      test (λ links → 1ℝ -ℝ test links)
      (λ links → oneMinusNN (test links) (bounded links))
      (λ links → oneMinusCompletes (test links))

  originalBoundedTestNegativeNumeratorUpper :
    (n : Nat)
    (test : OriginalOrder.WilsonTest
      theory traceData exponential beta oneLink bilateral divide
      ordered strictToWeak n) →
    (∀ links → absℝ (test links) ≤ℝ 1ℝ) →
    numerator n (λ links → -ℝ test links) ≤ℝ partition n
  originalBoundedTestNegativeNumeratorUpper n test bounded =
    OriginalOrder.originalWilsonNumeratorBelowItsPartition
      theory traceData exponential beta oneLink bilateral divide
      ordered strictToWeak n
      (λ links → -ℝ test links)
      (λ links → 1ℝ +ℝ test links)
      (λ links → onePlusNN (test links) (bounded links))
      (λ links → onePlusCompletes (test links))

  originalBoundedTestNegativeNumeratorIsNegation :
    (n : Nat)
    (test : OriginalOrder.WilsonTest
      theory traceData exponential beta oneLink bilateral divide
      ordered strictToWeak n) →
    numerator n (λ links → -ℝ test links)
      ≡ -ℝ (numerator n test)
  originalBoundedTestNegativeNumeratorIsNegation n test =
    trans
      (OriginalOrder.originalWilsonNumeratorCongruent
        theory traceData exponential beta oneLink bilateral divide
        ordered strictToWeak n
        (λ links → -ℝ test links)
        (λ links → (-ℝ 1ℝ) *ℝ test links)
        (λ links → negAsScale (test links)))
      (trans
        (Finite.numeratorScale
          (OriginalOrder.sourceIntegration
            theory traceData exponential beta oneLink bilateral divide
            ordered strictToWeak n)
          (-ℝ 1ℝ) test)
        (sym (negAsScale (numerator n test))))

  originalBoundedTestNumeratorAbsoluteAtMostPartition :
    (n : Nat)
    (test : OriginalOrder.WilsonTest
      theory traceData exponential beta oneLink bilateral divide
      ordered strictToWeak n) →
    (∀ links → absℝ (test links) ≤ℝ 1ℝ) →
    absℝ (numerator n test) ≤ℝ partition n
  originalBoundedTestNumeratorAbsoluteAtMostPartition n test bounded =
    absFromSignedBounds
      (numerator n test)
      (partition n)
      (originalBoundedTestNumeratorUpper n test bounded)
      (subst
        (λ value → value ≤ℝ partition n)
        (originalBoundedTestNegativeNumeratorIsNegation n test)
        (originalBoundedTestNegativeNumeratorUpper n test bounded))

  originalBoundedTestNormalizedAbsoluteAtMostOne :
    (n : Nat)
    (test : OriginalOrder.WilsonTest
      theory traceData exponential beta oneLink bilateral divide
      ordered strictToWeak n) →
    (∀ links → absℝ (test links) ≤ℝ 1ℝ) →
    absℝ
      (Physical.normalizedExpectation
        (OriginalOrder.wilsonMeasure
          theory traceData exponential beta oneLink bilateral divide
          ordered strictToWeak n) test)
      ≤ℝ 1ℝ
  originalBoundedTestNormalizedAbsoluteAtMostOne n test bounded =
    divideSignedUnitBound
      (numerator n test) (partition n)
      (OriginalOrder.originalWilsonPartitionStrictlyPositive
        theory traceData exponential beta oneLink bilateral divide
        ordered strictToWeak strict n)
      (originalBoundedTestNumeratorAbsoluteAtMostPartition n test bounded)

  -- P0.06 original same-source WEXT/R445 two-measure version:
  -- selected n=1 bare word vs its actual native block pullback
  -- integrated in original interacting n=3 Wilson Gibbs/Haar.
  originalR445FineBlockedWordAbsoluteMomentAtMostOne :
    (w : OriginalWord 1) →
    absℝ
      (Physical.normalizedExpectation
        (OriginalOrder.wilsonMeasure
          theory traceData exponential beta oneLink bilateral divide
          ordered strictToWeak 3)
        (λ fine →
          originalWordTest 1 w
            (Push.actualBlockedLinkMap
              theory traceData exponential (beta 3)
              oneLink bilateral divide fine)))
      ≤ℝ 1ℝ
  originalR445FineBlockedWordAbsoluteMomentAtMostOne w =
    originalBoundedTestNormalizedAbsoluteAtMostOne
      3
      (λ fine →
        originalWordTest 1 w
          (Push.actualBlockedLinkMap
            theory traceData exponential (beta 3)
            oneLink bilateral divide fine))
      (λ fine →
        originalWordAbsBelowOne 1 w
          (Push.actualBlockedLinkMap
            theory traceData exponential (beta 3)
            oneLink bilateral divide fine))

  originalR445BareWordAbsoluteMomentAtMostOne :
    (w : OriginalWord 1) →
    absℝ
      (Physical.normalizedExpectation
        (OriginalOrder.wilsonMeasure
          theory traceData exponential beta oneLink bilateral divide
          ordered strictToWeak 1)
        (originalWordTest 1 w))
      ≤ℝ 1ℝ
  originalR445BareWordAbsoluteMomentAtMostOne w =
    originalBoundedTestNormalizedAbsoluteAtMostOne
      1 (originalWordTest 1 w)
      (originalWordAbsBelowOne 1 w)
