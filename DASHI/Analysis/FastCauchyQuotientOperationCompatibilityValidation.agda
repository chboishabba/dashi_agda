module DASHI.Analysis.FastCauchyQuotientOperationCompatibilityValidation where

import DASHI.Analysis.FastCauchyReals as Fast
import DASHI.Analysis.FastCauchyQuotient as Quotient
import DASHI.Analysis.FastCauchyConstructedRealBackendExact as Backend
import DASHI.Analysis.SetoidComplexQuotientWeldExact as ComplexWeld
import DASHI.Analysis.FastCauchyQuotientOperationCompatibilityExact as P

compatibilityCompilerRegression :
  ∀ {A : Fast.RationalMetricAuthority}
    {O : Fast.FastCauchyOperations A}
    {Q : Quotient.SetQuotientBackend (Fast.FastCauchyReal A) Fast._≈R_} →
  (packaging : Backend.FastCauchyBackendPackaging A O) →
  (F : Quotient.FastCauchyQuotientOperations A O Q) →
  (L : Quotient.FastCauchyQuotientAlgebraLaws A O Q F) →
  (C : Quotient.FastCauchyQuotientCompleteness A O Q) →
  ComplexWeld.PropositionalQuotientOperationCompatibility
    (Backend.fastCauchySetoidOrderedCompleteReal O packaging)
    (P.fastCauchyNewSpineQuotient packaging F L C)
compatibilityCompilerRegression =
  P.fastCauchyQuotientOperationCompatibility
