module DASHI.Physics.YangMills.YMClayW1F19IntegratedCovarianceMomentWeldExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban, "Renormalization Group Approach to Lattice Gauge Field
-- Theories. I", Communications in Mathematical Physics 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223.
--
-- Tadeusz Bałaban, "Large Field Renormalization. I", Communications in
-- Mathematical Physics 122 (1989), 175--202. DOI: 10.1007/BF01257412.
--
-- DASHI CONTRIBUTION
--
-- Compile the W1 normalized covariance from the SAME original F19 four-mark
-- source moments.  The fine and coarse expressions agree after quotienting
-- the 1, F, G and FG coefficients by the one original fine/coarse normalizer.
-- This is moment recovery and finite algebra, not a new physical bound.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Vec.Base using (Vec)
open import Relation.Binary.PropositionalEquality using (cong; trans)

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ; 0ℝ; _*ℝ_; _-ℝ_; _<ℝ_)
import DASHI.Physics.Closure.NSPeriodicModeInverseNormScaling as Scaling
import DASHI.Physics.YangMills.SUNMatrixCarrier as SUN
import DASHI.Physics.YangMills.YMClaySUNMatrixWilsonTraceCoreExact as Trace
import DASHI.Physics.YangMills.YMClayStrictPositiveRealExponentialCoreExact as Exp
import DASHI.Physics.YangMills.YMClayFiniteProductHaarPermutationExact as Product
import DASHI.Physics.YangMills.YMClayFiniteProductHaarOrderedAlgebraExact as Ordered
import DASHI.Physics.YangMills.YMClaySUNProductHaarGaugeFromOneLinkExact as Bilateral
import DASHI.Physics.YangMills.YMClaySUNWeightedDisjointPairFibreReparamExact as Fibre
import DASHI.Physics.YangMills.YMClayOriginalWilsonF19FineTwoMarkMomentBIDIExact as Fine
import DASHI.Physics.YangMills.YMClayW0OriginalF19CandidateEquation171TExact as W0
import DASHI.Physics.YangMills.YMClayW1F19AffineCovarianceExact as W1
open import DASHI.Physics.YangMills.CompactLieProofLevel

record NormalizedExpectation : Set₁ where
  field
    quotient : ℝ → ℝ → ℝ
    quotientNumeratorCongruent :
      ∀ numerator numerator′ denominator →
      numerator ≡ numerator′ →
      quotient numerator denominator ≡ quotient numerator′ denominator
    quotientDenominatorCongruent :
      ∀ numerator denominator denominator′ →
      denominator ≡ denominator′ →
      quotient numerator denominator ≡ quotient numerator denominator′

open NormalizedExpectation public

quotientFromInverseAuthority :
  Scaling.OrderedRealInverseAuthority →
  NormalizedExpectation
quotientFromInverseAuthority realInverse = record
  { quotient =
      λ numerator denominator →
        numerator *ℝ Scaling.reciprocal realInverse denominator
  ; quotientNumeratorCongruent =
      λ numerator numerator′ denominator equality →
        cong
          (λ value → value *ℝ Scaling.reciprocal realInverse denominator)
          equality
  ; quotientDenominatorCongruent =
      λ numerator denominator denominator′ equality →
        cong
          (λ value → numerator *ℝ Scaling.reciprocal realInverse value)
          equality
  }

module _
    {Matrix Complex : Set} {N : Nat}
    (theory : SUN.CertifiedSUNMatrixTheory N Matrix Complex)
    (traceData : Trace.SUNMatrixRealTrace {Scalar = ℝ} theory)
    (exponential : Exp.StrictPositiveRealExponential)
    (beta : ℝ)
    (source : Product.OneLinkProductHaar (SUN.SUNMatrixElement theory))
    (bilateral : Bilateral.OneLinkSUNBilateralHaar theory source)
    (linear : Ordered.OneLinkOrderedHaarAlgebra source)
  where

  Link : Set
  Link = SUN.SUNMatrixElement theory

  Pair : Set
  Pair = Fibre.Pair theory source bilateral

  FineTest : Set
  FineTest = Vec Pair 64 → Vec Link 896 → ℝ

  SlowField : Set
  SlowField = Vec Link 64

  fineZ : ℝ
  fineZ =
    Fine.originalFineCoefficient
      theory traceData exponential beta source bilateral linear
      (Fine.originalFineWilsonWeight
        theory traceData exponential beta source bilateral linear)

  coarseZ : ℝ
  coarseZ =
    Product.productIntegral source
      (W0.sourceK0 theory traceData exponential beta source bilateral linear)

  fineF : FineTest → ℝ
  fineF left =
    Fine.originalFineCoefficient
      theory traceData exponential beta source bilateral linear
      (Fine.originalWilsonFineF
        theory traceData exponential beta source bilateral linear left)

  coarseF : FineTest → ℝ
  coarseF left =
    Product.productIntegral source
      (W0.sourceKF theory traceData exponential beta source bilateral linear left)

  fineG : FineTest → ℝ
  fineG right =
    Fine.originalFineCoefficient
      theory traceData exponential beta source bilateral linear
      (Fine.originalWilsonFineF
        theory traceData exponential beta source bilateral linear right)

  coarseG : FineTest → ℝ
  coarseG right =
    Product.productIntegral source
      (W0.sourceKG theory traceData exponential beta source bilateral linear right)

  fineFG : FineTest → FineTest → ℝ
  fineFG left right =
    Fine.originalFineCoefficient
      theory traceData exponential beta source bilateral linear
      (Fine.originalWilsonFineFG
        theory traceData exponential beta source bilateral linear left right)

  coarseFG : FineTest → FineTest → ℝ
  coarseFG left right =
    Product.productIntegral source
      (W0.sourceKFG
        theory traceData exponential beta source bilateral linear left right)

  fineNormalizerEqualsCoarseNormalizer : fineZ ≡ coarseZ
  fineNormalizerEqualsCoarseNormalizer =
    W0.physicalFineZEqualsCoarseCandidateT
      theory traceData exponential beta source bilateral linear

  fineFEqualsCoarseF : ∀ left → fineF left ≡ coarseF left
  fineFEqualsCoarseF left =
    W0.physicalFineFEqualsCoarseCandidateT
      theory traceData exponential beta source bilateral linear left

  fineGEqualsCoarseG : ∀ right → fineG right ≡ coarseG right
  fineGEqualsCoarseG right =
    W0.physicalFineGEqualsCoarseCandidateT
      theory traceData exponential beta source bilateral linear right

  fineFGEqualsCoarseFG :
    ∀ left right → fineFG left right ≡ coarseFG left right
  fineFGEqualsCoarseFG left right =
    W0.physicalFineFGEqualsCoarseCandidateT
      theory traceData exponential beta source bilateral linear left right

  normalizedFineF :
    (normalization : NormalizedExpectation) →
    ∀ left →
      quotient normalization (fineF left) fineZ
        ≡ quotient normalization (coarseF left) coarseZ
  normalizedFineF normalization left =
    trans
      (quotientNumeratorCongruent normalization
        (fineF left) (coarseF left) fineZ
        (fineFEqualsCoarseF left))
      (quotientDenominatorCongruent normalization
        (coarseF left) fineZ coarseZ
        fineNormalizerEqualsCoarseNormalizer)

  normalizedFineG :
    (normalization : NormalizedExpectation) →
    ∀ right →
      quotient normalization (fineG right) fineZ
        ≡ quotient normalization (coarseG right) coarseZ
  normalizedFineG normalization right =
    trans
      (quotientNumeratorCongruent normalization
        (fineG right) (coarseG right) fineZ
        (fineGEqualsCoarseG right))
      (quotientDenominatorCongruent normalization
        (coarseG right) fineZ coarseZ
        fineNormalizerEqualsCoarseNormalizer)

  normalizedFineFG :
    (normalization : NormalizedExpectation) →
    ∀ left right →
      quotient normalization (fineFG left right) fineZ
        ≡ quotient normalization (coarseFG left right) coarseZ
  normalizedFineFG normalization left right =
    trans
      (quotientNumeratorCongruent normalization
        (fineFG left right) (coarseFG left right) fineZ
        (fineFGEqualsCoarseFG left right))
      (quotientDenominatorCongruent normalization
        (coarseFG left right) fineZ coarseZ
        fineNormalizerEqualsCoarseNormalizer)

  fineCovariance :
    (normalization : NormalizedExpectation) →
    FineTest → FineTest → ℝ
  fineCovariance normalization left right =
    quotient normalization (fineFG left right) fineZ
      -ℝ (quotient normalization (fineF left) fineZ)
        *ℝ (quotient normalization (fineG right) fineZ)

  coarseCovariance :
    (normalization : NormalizedExpectation) →
    FineTest → FineTest → ℝ
  coarseCovariance normalization left right =
    quotient normalization (coarseFG left right) coarseZ
      -ℝ (quotient normalization (coarseF left) coarseZ)
        *ℝ (quotient normalization (coarseG right) coarseZ)

  fineCovarianceEqualsCoarseCovariance :
    (normalization : NormalizedExpectation) →
    ∀ left right →
      fineCovariance normalization left right
        ≡ coarseCovariance normalization left right
  fineCovarianceEqualsCoarseCovariance normalization left right =
    trans
      (cong
        (λ value →
          value
            -ℝ (quotient normalization (fineF left) fineZ)
              *ℝ (quotient normalization (fineG right) fineZ))
        (normalizedFineFG normalization left right))
      (trans
        (cong
          (λ value →
            quotient normalization (coarseFG left right) coarseZ
              -ℝ value
                *ℝ (quotient normalization (fineG right) fineZ))
          (normalizedFineF normalization left))
        (cong
          (λ value →
            quotient normalization (coarseFG left right) coarseZ
              -ℝ (quotient normalization (coarseF left) coarseZ)
                *ℝ value)
          (normalizedFineG normalization right)))

  fineNormalizerStrictlyPositive :
    (strict : Ordered.OneLinkStrictlyPositiveIntegration source) →
    0ℝ <ℝ fineZ
  fineNormalizerStrictlyPositive strict =
    W1.sourceFinePartitionStrictlyPositive
      theory traceData exponential beta source bilateral linear strict

  coarseNormalizerStrictlyPositive :
    (strict : Ordered.OneLinkStrictlyPositiveIntegration source) →
    0ℝ <ℝ coarseZ
  coarseNormalizerStrictlyPositive strict =
    W1.sourceCoarsePartitionStrictlyPositive
      theory traceData exponential beta source bilateral linear strict

  w1F19IntegratedCovarianceMomentWeldLevel : ProofLevel
  w1F19IntegratedCovarianceMomentWeldLevel = machineChecked
