module DASHI.Physics.YangMills.YMClayW1SourceFamilyNormalizedCovarianceWeldExact where

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
-- Factor the already kernel-accepted W1 normalized covariance weld into a
-- source-family interface.  The interface records only the four marked
-- moment columns and the common normalizer.  The generic theorem below is a
-- finite quotient congruence; it neither supplies nor replaces the physical
-- source, positivity, Haar, or inverse obligations of any particular scale.
-- The side-four member reuses the existing original F19/W0/W1 columns by
-- definition and is not a new physical claim.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Vec.Base using (Vec)
open import Relation.Binary.PropositionalEquality using (cong; trans)

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ; _*ℝ_; _-ℝ_)
import DASHI.Physics.YangMills.SUNMatrixCarrier as SUN
import DASHI.Physics.YangMills.YMClaySUNMatrixWilsonTraceCoreExact as Trace
import DASHI.Physics.YangMills.YMClayStrictPositiveRealExponentialCoreExact as Exp
import DASHI.Physics.YangMills.YMClayFiniteProductHaarPermutationExact as Product
import DASHI.Physics.YangMills.YMClayFiniteProductHaarOrderedAlgebraExact as Ordered
import DASHI.Physics.YangMills.YMClaySUNProductHaarGaugeFromOneLinkExact as Bilateral
import DASHI.Physics.YangMills.YMClaySUNWeightedDisjointPairFibreReparamExact as Fibre
import DASHI.Physics.YangMills.YMClayW1F19IntegratedCovarianceMomentWeldExact as Weld

record W1FourColumnSourceFamily (Test : Set) : Set₁ where
  field
    fineZ : ℝ
    coarseZ : ℝ
    fineF : Test → ℝ
    coarseF : Test → ℝ
    fineG : Test → ℝ
    coarseG : Test → ℝ
    fineFG : Test → Test → ℝ
    coarseFG : Test → Test → ℝ
    fineNormalizerEqualsCoarseNormalizer : fineZ ≡ coarseZ
    fineFEqualsCoarseF : ∀ left → fineF left ≡ coarseF left
    fineGEqualsCoarseG : ∀ right → fineG right ≡ coarseG right
    fineFGEqualsCoarseFG : ∀ left right → fineFG left right ≡ coarseFG left right

module _ {Test : Set} (family : W1FourColumnSourceFamily Test) where

  open W1FourColumnSourceFamily family

  normalizedFineF :
    (normalization : Weld.NormalizedExpectation) →
    ∀ left →
      Weld.quotient normalization (fineF left) fineZ
        ≡ Weld.quotient normalization (coarseF left) coarseZ
  normalizedFineF normalization left =
    trans
      (Weld.quotientNumeratorCongruent normalization
        (fineF left) (coarseF left) fineZ
        (fineFEqualsCoarseF left))
      (Weld.quotientDenominatorCongruent normalization
        (coarseF left) fineZ coarseZ
        fineNormalizerEqualsCoarseNormalizer)

  normalizedFineG :
    (normalization : Weld.NormalizedExpectation) →
    ∀ right →
      Weld.quotient normalization (fineG right) fineZ
        ≡ Weld.quotient normalization (coarseG right) coarseZ
  normalizedFineG normalization right =
    trans
      (Weld.quotientNumeratorCongruent normalization
        (fineG right) (coarseG right) fineZ
        (fineGEqualsCoarseG right))
      (Weld.quotientDenominatorCongruent normalization
        (coarseG right) fineZ coarseZ
        fineNormalizerEqualsCoarseNormalizer)

  normalizedFineFG :
    (normalization : Weld.NormalizedExpectation) →
    ∀ left right →
      Weld.quotient normalization (fineFG left right) fineZ
        ≡ Weld.quotient normalization (coarseFG left right) coarseZ
  normalizedFineFG normalization left right =
    trans
      (Weld.quotientNumeratorCongruent normalization
        (fineFG left right) (coarseFG left right) fineZ
        (fineFGEqualsCoarseFG left right))
      (Weld.quotientDenominatorCongruent normalization
        (coarseFG left right) fineZ coarseZ
        fineNormalizerEqualsCoarseNormalizer)

  fineCovariance :
    (normalization : Weld.NormalizedExpectation) →
    Test → Test → ℝ
  fineCovariance normalization left right =
    Weld.quotient normalization (fineFG left right) fineZ
      -ℝ (Weld.quotient normalization (fineF left) fineZ)
        *ℝ (Weld.quotient normalization (fineG right) fineZ)

  coarseCovariance :
    (normalization : Weld.NormalizedExpectation) →
    Test → Test → ℝ
  coarseCovariance normalization left right =
    Weld.quotient normalization (coarseFG left right) coarseZ
      -ℝ (Weld.quotient normalization (coarseF left) coarseZ)
        *ℝ (Weld.quotient normalization (coarseG right) coarseZ)

  covarianceEqual :
    (normalization : Weld.NormalizedExpectation) →
    ∀ left right →
      fineCovariance normalization left right
        ≡ coarseCovariance normalization left right
  covarianceEqual normalization left right =
    trans
      (cong
        (λ value →
          value
            -ℝ (Weld.quotient normalization (fineF left) fineZ)
              *ℝ (Weld.quotient normalization (fineG right) fineZ))
        (normalizedFineFG normalization left right))
      (trans
        (cong
          (λ value →
            Weld.quotient normalization (coarseFG left right) coarseZ
              -ℝ value
                *ℝ (Weld.quotient normalization (fineG right) fineZ))
          (normalizedFineF normalization left))
        (cong
          (λ value →
            Weld.quotient normalization (coarseFG left right) coarseZ
              -ℝ (Weld.quotient normalization (coarseF left) coarseZ)
                *ℝ value)
          (normalizedFineG normalization right)))

record W1IndexedSourceFamily (Index Test : Set) : Set₁ where
  field
    familyAt : Index → W1FourColumnSourceFamily Test

module _ {Index Test : Set} (family : W1IndexedSourceFamily Index Test) where

  covarianceEqualAt :
    (index : Index) →
    (normalization : Weld.NormalizedExpectation) →
    ∀ left right →
      fineCovariance
        (W1IndexedSourceFamily.familyAt family index)
        normalization left right
        ≡ coarseCovariance
            (W1IndexedSourceFamily.familyAt family index)
            normalization left right
  covarianceEqualAt index normalization left right =
    covarianceEqual
      (W1IndexedSourceFamily.familyAt family index)
      normalization left right

module _ {Matrix Complex : Set} {N : Nat}
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

  SideFourFineTest : Set
  SideFourFineTest = Vec Pair 64 → Vec Link 896 → ℝ

  sideFourW1FourColumnSourceFamily :
    W1FourColumnSourceFamily SideFourFineTest
  sideFourW1FourColumnSourceFamily = record
    { fineZ =
        Weld.fineZ theory traceData exponential beta source bilateral linear
    ; coarseZ =
        Weld.coarseZ theory traceData exponential beta source bilateral linear
    ; fineF =
        Weld.fineF theory traceData exponential beta source bilateral linear
    ; coarseF =
        Weld.coarseF theory traceData exponential beta source bilateral linear
    ; fineG =
        Weld.fineG theory traceData exponential beta source bilateral linear
    ; coarseG =
        Weld.coarseG theory traceData exponential beta source bilateral linear
    ; fineFG =
        Weld.fineFG theory traceData exponential beta source bilateral linear
    ; coarseFG =
        Weld.coarseFG theory traceData exponential beta source bilateral linear
    ; fineNormalizerEqualsCoarseNormalizer =
        Weld.fineNormalizerEqualsCoarseNormalizer
          theory traceData exponential beta source bilateral linear
    ; fineFEqualsCoarseF =
        Weld.fineFEqualsCoarseF
          theory traceData exponential beta source bilateral linear
    ; fineGEqualsCoarseG =
        Weld.fineGEqualsCoarseG
          theory traceData exponential beta source bilateral linear
    ; fineFGEqualsCoarseFG =
        Weld.fineFGEqualsCoarseFG
          theory traceData exponential beta source bilateral linear
    }

  sideFourFamilyCovarianceIsWeldCovariance :
    (normalization : Weld.NormalizedExpectation) →
    ∀ left right →
      covarianceEqual sideFourW1FourColumnSourceFamily
        normalization left right
        ≡ Weld.fineCovarianceEqualsCoarseCovariance
            theory traceData exponential beta source bilateral linear
            normalization left right
  sideFourFamilyCovarianceIsWeldCovariance normalization left right = refl
