module DASHI.Analysis.FastCauchySetQuotientComplexCompatibilityExact where

------------------------------------------------------------------------
-- FAST-CAUCHY SET QUOTIENT -> COMPLEX QUOTIENT OPERATION COMPATIBILITY
--
-- DASHI CONTRIBUTION
--
-- FastCauchyQuotient already defines quotient arithmetic by the eliminators
-- lift₁ / lift₂. Their beta laws therefore prove that quotienting a
-- representative commutes with zero, one, add, sub, mul, neg and abs.
--
-- This discharges the operation-compatibility input required by
-- SetoidComplexQuotientWeldExact for every FastCauchy quotient built through
-- that existing constructor. The concrete SetQuotientBackend itself remains
-- a separate, genuinely unpaid foundation input.
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
  (operations : Quotient.FastCauchyQuotientOperations A O Q) →
  Quotient.FastCauchyQuotientAlgebraLaws A O Q operations →
  Quotient.FastCauchyQuotientCompleteness A O Q →
  Fast.FastCauchyQuotientRealization A O
fastCauchyLegacyRealization =
  Quotient.fastCauchyQuotientRealization

fastCauchyPropositionalQuotient :
  ∀ {A : Fast.RationalMetricAuthority}
    {O : Fast.FastCauchyOperations A}
    {Q : Quotient.SetQuotientBackend (Fast.FastCauchyReal A) Fast._≈R_} →
  (packaging : Backend.FastCauchyBackendPackaging A O) →
  (operations : Quotient.FastCauchyQuotientOperations A O Q) →
  (laws : Quotient.FastCauchyQuotientAlgebraLaws A O Q operations) →
  (completeness : Quotient.FastCauchyQuotientCompleteness A O Q) →
  Spine.PropositionalQuotientRealization
    (Backend.fastCauchySetoidOrderedCompleteReal O packaging)
fastCauchyPropositionalQuotient
    packaging operations laws completeness =
  LegacyWeld.fastCauchyLegacyQuotientWeld
    packaging
    (fastCauchyLegacyRealization operations laws completeness)

fastCauchyQuotientOperationCompatibility :
  ∀ {A : Fast.RationalMetricAuthority}
    {O : Fast.FastCauchyOperations A}
    {Q : Quotient.SetQuotientBackend (Fast.FastCauchyReal A) Fast._≈R_}
    (packaging : Backend.FastCauchyBackendPackaging A O)
    (operations : Quotient.FastCauchyQuotientOperations A O Q)
    (laws : Quotient.FastCauchyQuotientAlgebraLaws A O Q operations)
    (completeness : Quotient.FastCauchyQuotientCompleteness A O Q) →
  ComplexWeld.PropositionalQuotientOperationCompatibility
    (Backend.fastCauchySetoidOrderedCompleteReal O packaging)
    (fastCauchyPropositionalQuotient
      packaging operations laws completeness)
fastCauchyQuotientOperationCompatibility
    {O = O} {Q = Q}
    packaging operations laws completeness = record
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
              (Quotient.negRespectRepresentative operations x≈y))
          value)
  ; ComplexWeld.quotientAbs = λ value →
      sym
        (Quotient.lift₁β Q
          (λ x → Quotient.inject Q (Fast.absR O x))
          (λ x≈y →
            Quotient.sound Q
              (Quotient.absRespectRepresentative operations x≈y))
          value)
  }
