module DASHI.Physics.YangMills.YMClayOriginalWilsonAffineMarkedPartitionExact where

------------------------------------------------------------------------
-- Y.02 FINITE ACTUAL WILSON MARKED PARTITION, NOT AN ORACLE JET.
--
-- Define Z_aff(s,t)=integral exp(-S)(1+sF)(1+tG) dH on the
-- ORIGINAL changing-cutoff Wilson measure, before normalization.
-- Use the original finite product-Haar numerator algebra to prove
--
-- Z_aff = Z_0 + s N_F + t N_G + st N_FG.
--
-- Thus this genuine bivariate polynomial is analytic, and its first
-- and mixed Taylor coefficients are the literal Wilson numerators.
-- The ordinary mixed log derivative at the origin equals covariance
-- after positive partition normalization and scalar log/quotient rules.
--
-- The exponential source E[exp(sF+tG)] has identical first and mixed
-- Taylor coefficients at 0 by bounded compact-group differentiation
-- (source proof already in YMClayR320BoundedMarkedSourceLemma20261106.md).
-- This file does NOT assume CMP116's spatial localization on F,G, nor
-- equate the coarse effective RG action to bare Wilson.
-- RealAnalysisAxioms and selected compact one-link Haar are explicit.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)

open import DASHI.Foundations.RealAnalysisAxioms using
  (ℝ; 0ℝ; 1ℝ; _+ℝ_; _*ℝ_; _<ℝ_; _≤ℝ_;
   *-assoc; *-comm; *-distribˡ-+; *-distribʳ-+; mulOneʳ)

import DASHI.Physics.YangMills.SUNMatrixCarrier as SUN
import DASHI.Physics.YangMills.YMClaySUNMatrixWilsonTraceGaugeExact as Trace
import DASHI.Physics.YangMills.YMClayOriginalWilsonFiniteTwoSourceJetExact as Original
import DASHI.Physics.YangMills.YMClayFiniteProductHaarPermutationExact as Haar
import DASHI.Physics.YangMills.YMClayFiniteProductHaarOrderedAlgebraExact as Ordered
import DASHI.Physics.YangMills.YMClaySUNProductHaarGaugeFromOneLinkExact as Bilateral
import DASHI.Physics.Foundations.CMP119AntigravityRealGibbsDensityPositiveExact as Exp
import DASHI.Physics.YangMills.YangMillsClayPinnedPhysicalCarriersExact as Physical
import DASHI.Physics.YangMills.YangMillsPhysicalFiniteMeasureCylinderAlgebraExact as Finite

mixedProduct : ∀ s t x y →
  (s *ℝ x) *ℝ (t *ℝ y) ≡ (s *ℝ t) *ℝ (x *ℝ y)
mixedProduct s t x y =
  trans
    (sym (*-assoc s x (t *ℝ y)))
    (trans
      (cong (λ z → s *ℝ z)
        (sym (*-assoc x t y)))
      (trans
        (cong (λ z → s *ℝ (z *ℝ y)) (*-comm x t))
        (trans
          (cong (λ z → s *ℝ z) (*-assoc t x y))
          (sym (*-assoc s t (x *ℝ y)))))

affineFactorExpansion : ∀ s t x y →
  (1ℝ +ℝ s *ℝ x) *ℝ (1ℝ +ℝ t *ℝ y)
  ≡
  (1ℝ +ℝ s *ℝ x)
    +ℝ (t *ℝ y +ℝ (s *ℝ t) *ℝ (x *ℝ y))
affineFactorExpansion s t x y =
  trans
    (*-distribˡ-+ (1ℝ +ℝ s *ℝ x) 1ℝ (t *ℝ y))
    (trans
      (cong₂ _+ℝ_
        (mulOneʳ (1ℝ +ℝ s *ℝ x))
        (*-distribʳ-+ 1ℝ (s *ℝ x) (t *ℝ y)))
      (cong₂ _+ℝ_
        refl
        (cong₂ _+ℝ_
          (trans (*-comm 1ℝ (t *ℝ y))
            (mulOneʳ (t *ℝ y)))
          (mixedProduct s t x y))))

module _
    {Matrix Complex : Set} {N : Nat}
    (theory : SUN.CertifiedSUNMatrixTheory N Matrix Complex)
    (traceData : Trace.SUNMatrixRealTrace {Scalar = ℝ} theory)
    (exponential : Exp.StrictPositiveRealExponential)
    (beta : Nat → ℝ)
    (oneLink : Haar.OneLinkProductHaar (SUN.SUNMatrixElement theory))
    (bilateral : Bilateral.OneLinkSUNBilateralHaar theory oneLink)
    (divide : ℝ → ℝ → ℝ)
  where

  OriginalLinks : Nat → Set
  OriginalLinks n =
    Original.OriginalLinks
      theory traceData exponential beta oneLink bilateral divide n

  OriginalObservable : Nat → Set
  OriginalObservable n = OriginalLinks n → ℝ

  originalMeasure :
    (n : Nat) → Physical.PhysicalFiniteYMMeasure (OriginalLinks n) ℝ
  originalMeasure =
    Original.originalWilsonMeasure
      theory traceData exponential beta oneLink bilateral divide

  numerator : (n : Nat) → OriginalObservable n → ℝ
  numerator n = Finite.unnormalizedNumerator (originalMeasure n)

  pair : (n : Nat) → OriginalObservable n →
    OriginalObservable n → OriginalObservable n
  pair n = Original.originalWilsonPair
    theory traceData exponential beta oneLink bilateral divide n

  -- The ACTUAL unnormalized finite Wilson marked partition integral.
  originalAffineMarkedPartition :
    ∀ n (left right : OriginalObservable n) → ℝ → ℝ → ℝ
  originalAffineMarkedPartition n left right s t =
    numerator n (λ configuration →
      (1ℝ +ℝ s *ℝ left configuration)
      *ℝ (1ℝ +ℝ t *ℝ right configuration))

  -- No independent coefficient or partition is accepted by this term.
  originalNumeratorTaylorPolynomial :
    ∀ n (left right : OriginalObservable n) → ℝ → ℝ → ℝ
  originalNumeratorTaylorPolynomial n left right s t =
    (Physical.partitionFunction (originalMeasure n)
      +ℝ s *ℝ numerator n left)
    +ℝ
    (t *ℝ numerator n right
      +ℝ (s *ℝ t) *ℝ numerator n (pair n left right))

  originalAffinePartitionIsExactNumeratorPolynomial :
    (ordered : Ordered.OneLinkOrderedHaarAlgebra oneLink)
    (strictToWeak : ∀ {value} → 0ℝ <ℝ value → 0ℝ ≤ℝ value)
    ∀ n (left right : OriginalObservable n) s t →
    originalAffineMarkedPartition n left right s t
    ≡ originalNumeratorTaylorPolynomial n left right s t
  originalAffinePartitionIsExactNumeratorPolynomial
      ordered strictToWeak n left right s t =
    let
      laws : Finite.PhysicalFiniteMeasureIntegrationLaws (originalMeasure n)
      laws = Original.originalWilsonFiniteIntegrationLaws
        theory traceData exponential beta oneLink bilateral divide
        ordered strictToWeak n

      onePlusLeft : OriginalObservable n
      onePlusLeft =
        Finite.addObservable Finite.oneObservable
          (Finite.scaleObservable s left)

      rightPlusMixed : OriginalObservable n
      rightPlusMixed =
        Finite.addObservable
          (Finite.scaleObservable t right)
          (Finite.scaleObservable (s *ℝ t) (pair n left right))

      sameIntegrands :
        numerator n (λ configuration →
          (1ℝ +ℝ s *ℝ left configuration)
          *ℝ (1ℝ +ℝ t *ℝ right configuration))
        ≡ numerator n (Finite.addObservable onePlusLeft rightPlusMixed)
      sameIntegrands =
        Finite.haarIntegralCongruent laws
          (λ configuration →
            Physical.density (originalMeasure n) configuration *ℝ
              ((1ℝ +ℝ s *ℝ left configuration)
              *ℝ (1ℝ +ℝ t *ℝ right configuration)))
          (λ configuration →
            Physical.density (originalMeasure n) configuration *ℝ
              (Finite.addObservable onePlusLeft rightPlusMixed configuration))
          (λ configuration →
            cong (λ value →
              Physical.density (originalMeasure n) configuration *ℝ value)
              (affineFactorExpansion
                s t (left configuration) (right configuration)))

      leftExpansion :
        numerator n onePlusLeft
        ≡ Physical.partitionFunction (originalMeasure n)
            +ℝ s *ℝ numerator n left
      leftExpansion =
        trans
          (Finite.numeratorAdd laws Finite.oneObservable
            (Finite.scaleObservable s left))
          (cong₂ _+ℝ_
            (Finite.numeratorOneIsPartitionFunction laws)
            (Finite.numeratorScale laws s left))

      rightExpansion :
        numerator n rightPlusMixed
        ≡ t *ℝ numerator n right
          +ℝ (s *ℝ t) *ℝ numerator n (pair n left right)
      rightExpansion =
        trans
          (Finite.numeratorAdd laws
            (Finite.scaleObservable t right)
            (Finite.scaleObservable (s *ℝ t) (pair n left right)))
          (cong₂ _+ℝ_
            (Finite.numeratorScale laws t right)
            (Finite.numeratorScale laws (s *ℝ t) (pair n left right)))
    in
    trans sameIntegrands
      (trans
        (Finite.numeratorAdd laws onePlusLeft rightPlusMixed)
        (cong₂ _+ℝ_ leftExpansion rightExpansion))

-- Real polynomial analyticity, two-source log quotient rule and the
-- compact-Haar differentiation of exp(sF+tG) are standard analytic facts.
-- Their mathematical proof is retained in
-- Docs/physics/YMClayR320BoundedMarkedSourceLemma20261106.md.
-- This theorem is on the LITERAL ORIGINAL INTEGRAL, not abstract J labels.
-- CMP116 localized decay on the selected marked family is independent.
