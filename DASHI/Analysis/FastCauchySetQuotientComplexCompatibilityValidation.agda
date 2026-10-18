module DASHI.Analysis.FastCauchySetQuotientComplexCompatibilityValidation where

import DASHI.Analysis.FastCauchyReals as Fast
import DASHI.Analysis.FastCauchyQuotient as Quotient
import DASHI.Analysis.FastCauchyConstructedRealBackendExact as Backend
import DASHI.Analysis.ConstructedRealBackendSpineExact as Spine
import DASHI.Analysis.SetoidComplexQuotientWeldExact as ComplexWeld
import DASHI.Analysis.FastCauchySetQuotientComplexCompatibilityExact as P

compatibilityRegression :
  ∀ {A : Fast.RationalMetricAuthority}
    {O : Fast.FastCauchyOperations A}
    {Q : Quotient.SetQuotientBackend (Fast.FastCauchyReal A) Fast._≈R_} →
  (packaging : Backend.FastCauchyBackendPackaging A O) →
  (F : Quotient.FastCauchyQuotientOperations A O Q) →
  (L : Quotient.FastCauchyQuotientAlgebraLaws A O Q F) →
  (C : Quotient.FastCauchyQuotientCompleteness A O Q) →
  ComplexWeld.PropositionalQuotientOperationCompatibility
    (Backend.fastCauchySetoidOrderedCompleteReal O packaging)
    (P.fastCauchyPropositionalQuotient packaging F L C)
compatibilityRegression =
  P.fastCauchySetQuotientComplexCompatibility
