module DASHI.Analysis.FastCauchyQuotientOperationCompatibilityExact where

------------------------------------------------------------------------
-- FAST-CAUCHY QUOTIENT β-LAWS -> GENERIC COMPLEX-QUOTIENT COMPATIBILITY
--
-- DASHI CONTRIBUTION
--
-- FastCauchyQuotient constructs +,-,*,neg,abs on the quotient by lift₁/lift₂.
-- Therefore the compatibility equations consumed by
-- SetoidComplexQuotientWeldExact are not new mathematical assumptions: they
-- are exactly the corresponding quotient β-laws.
--
-- This owner compiles those β-laws into the newer generic compatibility
-- record.  It still does NOT construct the SetQuotientBackend, quotient field
-- laws, or quotient completeness package.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (sym)

import DASHI.Analysis.FastCauchyReals as Fast
import DASHI.Analysis.FastCauchyQuotient as Quotient
import DASHI.Analysis.FastCauchyConstructedRealBackendExact as Backend
import DASHI.Analysis.FastCauchyLegacyQuotientBackendWeldExact as LegacyWeld
import DASHI.Analysis.ConstructedRealBackendSpineExact as Spine
import DASHI.Analysis.SetoidComplexQuotientWeldExact as ComplexWeld

fastCauchyLegacyRealization :
  ∀ {A : Fast.RationalMetricAuthority}
    {O : Fast.FastCauchyOperations A}
    {Q : Quotient.SetQuotientBackend
      (Fast.FastCauchyReal A) Fast._≈R_} →
  (F : Quotient.FastCauchyQuotientOperations A O Q) →
  Quotient.FastCauchyQuotientAlgebraLaws A O Q F →
  Quotient.FastCauchyQuotientCompleteness A O Q →
  Fast.FastCauchyQuotientRealization A O
fastCauchyLegacyRealization =
  Quotient.fastCauchyQuotientRealization

fastCauchyNewSpineQuotient :
  ∀ {A : Fast.RationalMetricAuthority}
    {O : Fast.FastCauchyOperations A}
    {Q : Quotient.SetQuotientBackend
      (Fast.FastCauchyReal A) Fast._≈R_} →
  (packaging : Backend.FastCauchyBackendPackaging A O) →
  (F : Quotient.FastCauchyQuotientOperations A O Q) →
  (L : Quotient.FastCauchyQuotientAlgebraLaws A O Q F) →
  (C : Quotient.FastCauchyQuotientCompleteness A O Q) →
  Spine.PropositionalQuotientRealization
    (Backend.fastCauchySetoidOrderedCompleteReal O packaging)
fastCauchyNewSpineQuotient packaging F L C =
  LegacyWeld.fastCauchyLegacyQuotientWeld
    packaging
    (fastCauchyLegacyRealization F L C)

fastCauchyQuotientOperationCompatibility :
  ∀ {A : Fast.RationalMetricAuthority}
    {O : Fast.FastCauchyOperations A}
    {Q : Quotient.SetQuotientBackend
      (Fast.FastCauchyReal A) Fast._≈R_} →
  (packaging : Backend.FastCauchyBackendPackaging A O) →
  (F : Quotient.FastCauchyQuotientOperations A O Q) →
  (L : Quotient.FastCauchyQuotientAlgebraLaws A O Q F) →
  (C : Quotient.FastCauchyQuotientCompleteness A O Q) →
  ComplexWeld.PropositionalQuotientOperationCompatibility
    (Backend.fastCauchySetoidOrderedCompleteReal O packaging)
    (fastCauchyNewSpineQuotient packaging F L C)
fastCauchyQuotientOperationCompatibility
    {O = O} {Q = Q} packaging F L C = record
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
              (Quotient.negRespectRepresentative F x≈y))
          value)

  ; ComplexWeld.quotientAbs = λ value →
      sym
        (Quotient.lift₁β Q
          (λ x → Quotient.inject Q (Fast.absR O x))
          (λ x≈y →
            Quotient.sound Q
              (Quotient.absRespectRepresentative F x≈y))
          value)
  }
