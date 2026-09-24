module DASHI.Analysis.FastCauchySetQuotientComplexCompatibilityExact where

------------------------------------------------------------------------
-- FAST-CAUCHY SET-QUOTIENT -> COMPLEX RING COMPATIBILITY
--
-- DASHI CONTRIBUTION
--
-- The generic SetoidComplexQuotientWeld requires quotient compatibility for
-- zero, one, +, -, *, neg and abs.  For the repository's Fast-Cauchy quotient
-- these equations are not new assumptions: the quotient operations are built
-- with SetQuotientBackend.lift₁/lift₂, so compatibility on representatives is
-- exactly lift₁β/lift₂β.
--
-- This file does NOT construct a SetQuotientBackend.  It compiles any future
-- concrete backend plus the already-required quotient algebra/completeness
-- data into the compatibility record consumed by the complex weld.
------------------------------------------------------------------------

open import Relation.Binary.PropositionalEquality using (refl; sym)

import DASHI.Analysis.FastCauchyReals as Fast
import DASHI.Analysis.FastCauchyQuotient as Quotient
import DASHI.Analysis.FastCauchyConstructedRealBackendExact as Backend
import DASHI.Analysis.FastCauchyLegacyQuotientBackendWeldExact as LegacyWeld
import DASHI.Analysis.ConstructedRealBackendSpineExact as Spine
import DASHI.Analysis.SetoidComplexQuotientWeldExact as ComplexWeld

fastCauchyLegacyRealization :
  ∀ {A : Fast.RationalMetricAuthority}
    {O : Fast.FastCauchyOperations A}
    {Q : Quotient.SetQuotientBackend (Fast.FastCauchyReal A) Fast._≈R_} →
  (F : Quotient.FastCauchyQuotientOperations A O Q) →
  Quotient.FastCauchyQuotientAlgebraLaws A O Q F →
  Quotient.FastCauchyQuotientCompleteness A O Q →
  Fast.FastCauchyQuotientRealization A O
fastCauchyLegacyRealization =
  Quotient.fastCauchyQuotientRealization

fastCauchyPropositionalQuotient :
  ∀ {A : Fast.RationalMetricAuthority}
    {O : Fast.FastCauchyOperations A}
    {Q : Quotient.SetQuotientBackend (Fast.FastCauchyReal A) Fast._≈R_} →
  (packaging : Backend.FastCauchyBackendPackaging A O) →
  (F : Quotient.FastCauchyQuotientOperations A O Q) →
  (L : Quotient.FastCauchyQuotientAlgebraLaws A O Q F) →
  (C : Quotient.FastCauchyQuotientCompleteness A O Q) →
  Spine.PropositionalQuotientRealization
    (Backend.fastCauchySetoidOrderedCompleteReal O packaging)
fastCauchyPropositionalQuotient packaging F L C =
  LegacyWeld.fastCauchyLegacyQuotientWeld
    packaging
    (fastCauchyLegacyRealization F L C)

fastCauchySetQuotientComplexCompatibility :
  ∀ {A : Fast.RationalMetricAuthority}
    {O : Fast.FastCauchyOperations A}
    {Q : Quotient.SetQuotientBackend (Fast.FastCauchyReal A) Fast._≈R_} →
  (packaging : Backend.FastCauchyBackendPackaging A O) →
  (F : Quotient.FastCauchyQuotientOperations A O Q) →
  (L : Quotient.FastCauchyQuotientAlgebraLaws A O Q F) →
  (C : Quotient.FastCauchyQuotientCompleteness A O Q) →
  ComplexWeld.PropositionalQuotientOperationCompatibility
    (Backend.fastCauchySetoidOrderedCompleteReal O packaging)
    (fastCauchyPropositionalQuotient packaging F L C)
fastCauchySetQuotientComplexCompatibility
    {A} {O} {Q} packaging F L C = record
  { ComplexWeld.quotientZero = refl
  ; ComplexWeld.quotientOne = refl

  ; ComplexWeld.quotientAdd = λ left right →
      sym
        (Quotient.lift₂β Q
          (λ x y → Quotient.inject Q (Fast.addR O x y))
          (λ x≈x′ y≈y′ →
            Quotient.sound Q
              (Fast.addRespect O x≈x′ y≈y′))
          left right)

  ; ComplexWeld.quotientSub = λ left right →
      sym
        (Quotient.lift₂β Q
          (λ x y → Quotient.inject Q (Fast.subR O x y))
          (λ x≈x′ y≈y′ →
            Quotient.sound Q
              (Fast.subRespect O x≈x′ y≈y′))
          left right)

  ; ComplexWeld.quotientMul = λ left right →
      sym
        (Quotient.lift₂β Q
          (λ x y → Quotient.inject Q (Fast.mulR O x y))
          (λ x≈x′ y≈y′ →
            Quotient.sound Q
              (Fast.mulRespect O x≈x′ y≈y′))
          left right)

  ; ComplexWeld.quotientNeg = λ value →
      sym
        (Quotient.lift₁β Q
          (λ x → Quotient.inject Q (Fast.negR O x))
          (λ x≈y →
            Quotient.sound Q
              (Backend.negRespect packaging x≈y))
          value)

  ; ComplexWeld.quotientAbs = λ value →
      sym
        (Quotient.lift₁β Q
          (λ x → Quotient.inject Q (Fast.absR O x))
          (λ x≈y →
            Quotient.sound Q
              (Backend.absRespect packaging x≈y))
          value)
  }
