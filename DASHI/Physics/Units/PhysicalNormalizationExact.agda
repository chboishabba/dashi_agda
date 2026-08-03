module DASHI.Physics.Units.PhysicalNormalizationExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Author: Edgar Buckingham.
-- Title: "On Physically Similar Systems; Illustrations of the Use of
-- Dimensional Equations".
-- Physical Review 4 (1914), 345--376.
-- DOI: 10.1103/PhysRev.4.345.
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale--Kato--Majda Criterion with Optimal Frequency and Temporal
-- Localization".
-- Journal of Mathematical Fluid Mechanics 21 (2019), article 1.
-- DOI: 10.1007/s00021-019-0411-z.
-- arXiv DOI: 10.48550/arXiv.1803.05569.
--
-- PURPOSE
-- Separate general length/velocity nondimensionalization from the special
-- viscous choice U = nu/L.  The exact theorem below proves that the gradient
-- scale U/L and time scale L/U cancel, which is the algebraic heart of the
-- scale invariance of Luo's localized integral.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

record ScaleAlgebra (Scalar : Set) : Set where
  field
    one : Scalar
    _∙_ : Scalar → Scalar → Scalar
    associative : ∀ left middle right →
      (left ∙ middle) ∙ right ≡ left ∙ (middle ∙ right)
    identityLeft : ∀ value → one ∙ value ≡ value
    identityRight : ∀ value → value ∙ one ≡ value

open ScaleAlgebra public

record PositiveScale {Scalar : Set} (algebra : ScaleAlgebra Scalar) : Set where
  field
    value : Scalar
    inverse : Scalar
    inverseLeft :
      ScaleAlgebra._∙_ algebra inverse value ≡ ScaleAlgebra.one algebra
    inverseRight :
      ScaleAlgebra._∙_ algebra value inverse ≡ ScaleAlgebra.one algebra

open PositiveScale public

multiply :
  ∀ {Scalar} → ScaleAlgebra Scalar → Scalar → Scalar → Scalar
multiply algebra = ScaleAlgebra._∙_ algebra

gradientScale :
  ∀ {Scalar} (algebra : ScaleAlgebra Scalar) →
  PositiveScale algebra → PositiveScale algebra → Scalar
gradientScale algebra lengthScale velocityScale =
  multiply algebra (value velocityScale) (inverse lengthScale)

timeScale :
  ∀ {Scalar} (algebra : ScaleAlgebra Scalar) →
  PositiveScale algebra → PositiveScale algebra → Scalar
timeScale algebra lengthScale velocityScale =
  multiply algebra (value lengthScale) (inverse velocityScale)

------------------------------------------------------------------------
-- (U L^-1)(L U^-1) = 1.
------------------------------------------------------------------------

gradientScaleTimesTimeScaleIsOne :
  ∀ {Scalar}
    (algebra : ScaleAlgebra Scalar)
    (lengthScale velocityScale : PositiveScale algebra) →
  multiply algebra
    (gradientScale algebra lengthScale velocityScale)
    (timeScale algebra lengthScale velocityScale)
  ≡ ScaleAlgebra.one algebra
gradientScaleTimesTimeScaleIsOne algebra lengthScale velocityScale =
  trans
    (ScaleAlgebra.associative algebra
      (value velocityScale)
      (inverse lengthScale)
      (multiply algebra (value lengthScale) (inverse velocityScale)))
    (trans
      (cong
        (λ inner → multiply algebra (value velocityScale) inner)
        (sym
          (ScaleAlgebra.associative algebra
            (inverse lengthScale)
            (value lengthScale)
            (inverse velocityScale))))
      (trans
        (cong
          (λ inner → multiply algebra (value velocityScale)
            (multiply algebra inner (inverse velocityScale)))
          (inverseLeft lengthScale))
        (trans
          (cong
            (λ inner → multiply algebra (value velocityScale) inner)
            (ScaleAlgebra.identityLeft algebra (inverse velocityScale)))
          (inverseRight velocityScale))))

scaledLocalizedIntegral :
  ∀ {Scalar} →
  (algebra : ScaleAlgebra Scalar) →
  PositiveScale algebra → PositiveScale algebra → Scalar → Scalar
scaledLocalizedIntegral algebra lengthScale velocityScale normalizedIntegral =
  multiply algebra
    (multiply algebra
      (gradientScale algebra lengthScale velocityScale)
      (timeScale algebra lengthScale velocityScale))
    normalizedIntegral

localizedIntegralScaleInvariant :
  ∀ {Scalar}
    (algebra : ScaleAlgebra Scalar)
    (lengthScale velocityScale : PositiveScale algebra)
    (normalizedIntegral : Scalar) →
  scaledLocalizedIntegral algebra lengthScale velocityScale normalizedIntegral
  ≡ normalizedIntegral
localizedIntegralScaleInvariant algebra lengthScale velocityScale normalizedIntegral =
  trans
    (cong
      (λ scale → multiply algebra scale normalizedIntegral)
      (gradientScaleTimesTimeScaleIsOne
        algebra lengthScale velocityScale))
    (ScaleAlgebra.identityLeft algebra normalizedIntegral)

------------------------------------------------------------------------
-- General Reynolds normalization and Luo's special viscous selection.
--
-- Re = U L / nu.  Rather than introduce division at the foundational layer,
-- Re = 1 is represented by the exact multiplicative equality nu = U L.
------------------------------------------------------------------------

record ReynoldsOneSelection
    {Scalar : Set}
    (algebra : ScaleAlgebra Scalar)
    (lengthScale velocityScale viscosityScale : PositiveScale algebra) : Set where
  field
    viscosityEqualsVelocityTimesLength :
      value viscosityScale
      ≡ multiply algebra (value velocityScale) (value lengthScale)

open ReynoldsOneSelection public

record ViscousVelocitySelection
    {Scalar : Set}
    (algebra : ScaleAlgebra Scalar)
    (lengthScale velocityScale viscosityScale : PositiveScale algebra) : Set where
  field
    velocityEqualsViscosityPerLength :
      value velocityScale
      ≡ multiply algebra (value viscosityScale) (inverse lengthScale)
    reynoldsOne :
      ReynoldsOneSelection algebra lengthScale velocityScale viscosityScale

open ViscousVelocitySelection public

generalNormalizationRetained : Set
generalNormalizationRetained = ScaleAlgebra

luoUnitViscosityIsSpecialSelection :
  ∀ {Scalar}
    {algebra : ScaleAlgebra Scalar}
    {lengthScale velocityScale viscosityScale : PositiveScale algebra} →
  ViscousVelocitySelection
    algebra lengthScale velocityScale viscosityScale →
  ReynoldsOneSelection algebra lengthScale velocityScale viscosityScale
luoUnitViscosityIsSpecialSelection = reynoldsOne
