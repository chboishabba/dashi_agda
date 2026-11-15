module DASHI.Physics.YangMills.YMClayE1D1OriginalCrossNumeratorNormalizedMomentFactorExact where

------------------------------------------------------------------------
-- Actual original R445 fine-blocked versus bare Wilson Gibbs states.
--
-- Positive finite-source result: the genuine division-free cross
-- numerator is EXACTLY the difference of their source normalized
-- moments multiplied by the original two positive partitions.
--
-- X(F) = (E_f(F) - E_b(F)) * (Z_f * Z_b).
--
-- This is a derivation from the two ACTUAL Wilson numerators,
-- partitions, the original source positivity, and the explicitly
-- selected positive-division cancellation. No new physical measure,
-- normalized expectation oracle, RG rate or analyticity postulate.
--
-- The RealAnalysisAxioms module does not itself supply division;
-- the field law is an explicit argument, NOT claimed proved.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Data.List.Base using (_++_)
open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary.PropositionalEquality using
  (cong; cong₂; sym; trans)
open import DASHI.Foundations.RealAnalysisAxioms using
  (ℝ; 0ℝ; _<ℝ_; _≤ℝ_; _*ℝ_; _-ℝ_;
   *-assoc; *-comm; subMulDistributes)

import DASHI.Physics.YangMills.SUNMatrixCarrier as SUN
import DASHI.Physics.YangMills.YMClaySUNMatrixWilsonTraceGaugeExact as Trace
import DASHI.Physics.YangMills.YMClayFiniteProductHaarPermutationExact as Haar
import DASHI.Physics.YangMills.YMClayFiniteProductHaarOrderedAlgebraExact as Ordered
import DASHI.Physics.YangMills.YMClaySUNProductHaarGaugeFromOneLinkExact as Bilateral
import DASHI.Physics.Foundations.CMP119AntigravityRealGibbsDensityPositiveExact as Exp
import DASHI.Physics.YangMills.YMClayE1D1CrossNumeratorCenteringExact as Center
import DASHI.Physics.YangMills.YMClayOriginalWilsonFiniteNumeratorOrderExact as Numerator
import DASHI.Physics.YangMills.YMClayE1D1OriginalVariablePlaquetteWordsExact as Words
import DASHI.Physics.YangMills.YMClayE1D1OriginalWilsonWordConcatenationR445Exact as Conc

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
    (positiveDivisionCancels :
      (numerator denominator : ℝ) →
      0ℝ <ℝ denominator →
      divide numerator denominator *ℝ denominator ≡ numerator)
  where

  CoarseTest : Set
  CoarseTest =
    Center.CoarseTest
      theory traceData exponential beta oneLink bilateral divide
      ordered strictToWeak

  fineNumerator : CoarseTest → ℝ
  fineNumerator =
    Center.fineNumerator
      theory traceData exponential beta oneLink bilateral divide
      ordered strictToWeak

  bareNumerator : CoarseTest → ℝ
  bareNumerator =
    Center.bareNumerator
      theory traceData exponential beta oneLink bilateral divide
      ordered strictToWeak

  zFine : ℝ
  zFine = Center.zFine
    theory traceData exponential beta oneLink bilateral divide
    ordered strictToWeak

  zBare : ℝ
  zBare = Center.zBare
    theory traceData exponential beta oneLink bilateral divide
    ordered strictToWeak

  fineMoment : CoarseTest → ℝ
  fineMoment F = divide (fineNumerator F) zFine

  bareMoment : CoarseTest → ℝ
  bareMoment F = divide (bareNumerator F) zBare

  originalFinePartitionPositive : 0ℝ <ℝ zFine
  originalFinePartitionPositive =
    Numerator.originalWilsonPartitionStrictlyPositive
      theory traceData exponential beta oneLink bilateral divide
      ordered strictToWeak strict 3

  originalBarePartitionPositive : 0ℝ <ℝ zBare
  originalBarePartitionPositive =
    Numerator.originalWilsonPartitionStrictlyPositive
      theory traceData exponential beta oneLink bilateral divide
      ordered strictToWeak strict 1

  originalFineMomentTimesPartition :
    (F : CoarseTest) →
    fineMoment F *ℝ zFine ≡ fineNumerator F
  originalFineMomentTimesPartition F =
    positiveDivisionCancels
      (fineNumerator F) zFine originalFinePartitionPositive

  originalBareMomentTimesPartition :
    (F : CoarseTest) →
    bareMoment F *ℝ zBare ≡ bareNumerator F
  originalBareMomentTimesPartition F =
    positiveDivisionCancels
      (bareNumerator F) zBare originalBarePartitionPositive

  originalCrossNumeratorIsMomentDefectTimesPartitionProduct :
    (F : CoarseTest) →
    Center.X theory traceData exponential beta oneLink bilateral divide
      ordered strictToWeak F
    ≡
    (fineMoment F -ℝ bareMoment F) *ℝ (zFine *ℝ zBare)
  originalCrossNumeratorIsMomentDefectTimesPartitionProduct F =
    trans
      (cong₂ _-ℝ_
        (cong (λ numerator → numerator *ℝ zBare)
          (sym (originalFineMomentTimesPartition F)))
        (cong (λ numerator → numerator *ℝ zFine)
          (sym (originalBareMomentTimesPartition F))))
      (trans
        (cong₂ _-ℝ_
          (*-assoc (fineMoment F) zFine zBare)
          (trans
            (*-assoc (bareMoment F) zBare zFine)
            (cong (λ value → bareMoment F *ℝ value)
              (*-comm zBare zFine))))
        (sym
          (subMulDistributes
            (fineMoment F) (bareMoment F)
            (zFine *ℝ zBare))))

  -- Source-specific Wilson-word consequence: for the original
  -- coarse plaquette-word compiler, the test F*G is literally the
  -- concatenated original Wilson word. Thus the same X factorization
  -- applies to the *third* covariance insertion without an
  -- independent product-measure or word-factorization assumption.
  CoarseWord : Set
  CoarseWord =
    Words.PlaquetteWord
      theory traceData exponential beta oneLink bilateral divide 1

  coarseWordTest : CoarseWord → CoarseTest
  coarseWordTest =
    Words.originalWordObservable
      theory traceData exponential beta oneLink bilateral divide 1

  originalWordPairCrossNumeratorIsNormalizedDefect :
    (left right : CoarseWord) →
    Center.X theory traceData exponential beta oneLink bilateral divide
      ordered strictToWeak
      (λ coarse →
        coarseWordTest left coarse *ℝ coarseWordTest right coarse)
    ≡
    (fineMoment (coarseWordTest (left ++ right))
       -ℝ bareMoment (coarseWordTest (left ++ right)))
      *ℝ (zFine *ℝ zBare)
  originalWordPairCrossNumeratorIsNormalizedDefect left right =
    trans
      (Conc.originalR445WordProductCrossNumeratorIsConcatenation
        theory traceData exponential beta oneLink bilateral divide
        ordered strictToWeak left right)
      (originalCrossNumeratorIsMomentDefectTimesPartitionProduct
        (coarseWordTest (left ++ right)))

  -- This exact factorization is the only numerical algebra required
  -- before transporting a PHYSICAL X(F) error through positive
  -- division. It does NOT provide that physical error for any
  -- nonconstant original SU(N) plaquette or Wilson word.
