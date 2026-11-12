module DASHI.Physics.YangMills.YMClayP0BishopToOriginalWilsonRealWeldExact where

------------------------------------------------------------------------
-- P0: EXACT SCALAR-WELD CUT BETWEEN ORIGINAL WILSON AND BISHOP REAL.
--
-- On the pinned Bishop setoid the subtraction, cancellation and
-- positive reciprocal lemmas have genuine proof terms in
-- YMClayP0BishopRealCarrierInstancesExact.
--
-- The original finite Wilson model uses a DIFFERENT independently
-- postulated propositional ℝ in RealAnalysisAxioms. The missing step
-- is NOT cast/coercion. It is a faithful, operation-preserving
-- interpretation of that selected original scalar socket into the
-- constructed Bishop setoid, with a division map at positive inputs.
--
-- This module proves that ONE such semantic weld supplies both
-- pre-existing OriginalRealCenteringLaws and
-- OriginalRealPositiveDivisionLaws without NEW postulates.
--
-- The weld record is currently NOT INHABITED. It must never be
-- promoted as a completed real-field implementation, Agda-kernel
-- acceptance, or physical SU(N) RG theorem.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
import DASHI.Foundations.RealAnalysisAxioms as R
import Real as B
import RealProperties as P
import Inverse as Inv

import DASHI.Physics.YangMills.YMClayP0BishopRealCarrierInstancesExact as BishopP0
import DASHI.Physics.YangMills.YMClayE1D1CrossNumeratorCenteringAlgebraExact as WilsonP0

record OriginalWilsonToBishopScalarWeld
    (divide : R.ℝ → R.ℝ → R.ℝ) : Set₁ where
  field
    map : R.ℝ → B.ℝ
    reflectsEquality :
      ∀ {a b : R.ℝ} →
      B._≃_ (map a) (map b) → a ≡ b

    preserveZero : B._≃_ (map R.0ℝ) B.0ℝ
    preserveOne  : B._≃_ (map R.1ℝ) B.1ℝ
    preserveAdd :
      (a b : R.ℝ) →
      B._≃_ (map (R._+ℝ_ a b))
        (B._+_ (map a) (map b))
    preserveSub :
      (a b : R.ℝ) →
      B._≃_ (map (R._-ℝ_ a b))
        (B._-_ (map a) (map b))
    preserveMul :
      (a b : R.ℝ) →
      B._≃_ (map (R._*ℝ_ a b))
        (B._*_ (map a) (map b))
    preserveNeg :
      (a : R.ℝ) →
      B._≃_ (map (R.-ℝ a)) (B.-_ (map a))

    preservePositive :
      ∀ {d : R.ℝ} →
      R._<ℝ_ R.0ℝ d →
      B._<_ B.0ℝ (map d)

    preservePositiveDivision :
      (n d : R.ℝ) →
      (positive : R._<ℝ_ R.0ℝ d) →
      B._≃_
        (map (divide n d))
        (B._*_
          (map n)
          (Inv._⁻¹ (map d)
            (BishopP0.bishopPositiveDenominatorApartFromZero
              (map d) (preservePositive positive))))

open OriginalWilsonToBishopScalarWeld public

-- Propositional equality in the source implies setoid equality
-- of its interpreted image by ordinary Agda pattern matching.
sourceEqualityImpliesBishop :
  ∀ {divide : R.ℝ → R.ℝ → R.ℝ}
    (W : OriginalWilsonToBishopScalarWeld divide)
    {x y : R.ℝ} →
    x ≡ y →
    B._≃_ (map W x) (map W y)
sourceEqualityImpliesBishop W refl = P.≃-refl

-- P0.01 on the original selected ℝ, once the SAME-CARRIER WELD
-- is actually constructed, not by transporting untyped proof prose.
weldDerivesOriginalSubtractionAsNegation :
  ∀ {divide : R.ℝ → R.ℝ → R.ℝ}
    (W : OriginalWilsonToBishopScalarWeld divide)
    (x c : R.ℝ) →
    R._-ℝ_ x c
    ≡
    R._+ℝ_ x (R._*ℝ_ (R.-ℝ c) R.1ℝ)
weldDerivesOriginalSubtractionAsNegation W x c =
  reflectsEquality W
    (P.≃-trans
      (preserveSub W x c)
      (P.≃-trans
        (BishopP0.bishopSubtractionAsNegationTimesUnit
          (map W x) (map W c))
        (P.≃-trans
          (P.+-cong P.≃-refl
            (P.≃-trans
              (P.*-cong
                (P.≃-symm (preserveNeg W c))
                (P.≃-symm (preserveOne W)))
              (P.≃-symm
                (preserveMul W (R.-ℝ c) R.1ℝ))))
          (P.≃-symm
            (preserveAdd W x (R._*ℝ_ (R.-ℝ c) R.1ℝ))))))

weldDerivesOriginalSubtractionZeroRight :
  ∀ {divide : R.ℝ → R.ℝ → R.ℝ}
    (W : OriginalWilsonToBishopScalarWeld divide)
    (x : R.ℝ) →
    R._-ℝ_ x R.0ℝ ≡ x
weldDerivesOriginalSubtractionZeroRight W x =
  reflectsEquality W
    (P.≃-trans
      (preserveSub W x R.0ℝ)
      (P.≃-trans
        (P.+-cong
          P.≃-refl
          (P.-‿cong (preserveZero W)))
        (BishopP0.bishopSubtractionZeroRight (map W x))))

weldDerivesOriginalCenteredCancellation :
  ∀ {divide : R.ℝ → R.ℝ → R.ℝ}
    (W : OriginalWilsonToBishopScalarWeld divide)
    (numerator value partition : R.ℝ) →
    numerator ≡ R._*ℝ_ value partition →
    R._+ℝ_ numerator
      (R._*ℝ_ (R.-ℝ value) partition)
      ≡ R.0ℝ
weldDerivesOriginalCenteredCancellation W numerator value partition eq =
  reflectsEquality W
    (P.≃-trans
      (preserveAdd W numerator
        (R._*ℝ_ (R.-ℝ value) partition))
      (P.≃-trans
        (P.+-cong P.≃-refl
          (P.≃-trans
            (preserveMul W (R.-ℝ value) partition)
            (P.*-cong
              (preserveNeg W value) P.≃-refl)))
        (P.≃-trans
          (BishopP0.bishopCenteredScalarCancellation
            (map W numerator)
            (map W value)
            (map W partition)
            (P.≃-trans
              (sourceEqualityImpliesBishop W eq)
              (preserveMul W value partition)))
          (P.≃-symm (preserveZero W)))))

-- P0.03: an ORIGINAL-WILSON positive quotient reconstruction,
-- but only under a faithful semantic map preserving the specific
-- 'divide' operation. An arbitrary quotient parameter is not enough.
weldDerivesOriginalPositiveDivision :
  ∀ {divide : R.ℝ → R.ℝ → R.ℝ}
    (W : OriginalWilsonToBishopScalarWeld divide)
    (n d : R.ℝ) →
    (positive : R._<ℝ_ R.0ℝ d) →
    R._*ℝ_ (divide n d) d ≡ n
weldDerivesOriginalPositiveDivision W n d positive =
  reflectsEquality W
    (P.≃-trans
      (preserveMul W (divide n d) d)
      (P.≃-trans
        (P.*-cong (preservePositiveDivision W n d positive)
          P.≃-refl)
        (BishopP0.bishopPositiveQuotientTimesDenominator
          (map W n) (map W d) (preservePositive W positive))))

-- These are exact *constructed transformations*, not assumed fields.
weldSuppliesOriginalRealCenteringLaws :
  ∀ {divide : R.ℝ → R.ℝ → R.ℝ} →
  (W : OriginalWilsonToBishopScalarWeld divide) →
  WilsonP0.OriginalRealCenteringLaws
weldSuppliesOriginalRealCenteringLaws W = record
  { subtractionAsNegation =
      weldDerivesOriginalSubtractionAsNegation W
  ; subtractionZeroRight =
      weldDerivesOriginalSubtractionZeroRight W
  ; centeredCancellation =
      weldDerivesOriginalCenteredCancellation W
  }

weldSuppliesOriginalPositiveDivisionLaws :
  ∀ {divide : R.ℝ → R.ℝ → R.ℝ} →
  (W : OriginalWilsonToBishopScalarWeld divide) →
  WilsonP0.OriginalRealPositiveDivisionLaws divide
weldSuppliesOriginalPositiveDivisionLaws W = record
  { quotientTimesPositiveDenominator =
      weldDerivesOriginalPositiveDivision W
  }
