module DASHI.Analysis.FastCauchySetQuotientComplexCompatibilityValidation where

import DASHI.Analysis.FastCauchyReals as Fast
import DASHI.Analysis.FastCauchyQuotient as Quotient
import DASHI.Analysis.FastCauchyConstructedRealBackendExact as Backend
import DASHI.Analysis.FastCauchySetQuotientComplexCompatibilityExact as Exact
import DASHI.Analysis.SetoidComplexQuotientWeldExact as ComplexWeld

compatibilityCompiled :
  ∀ {A : Fast.RationalMetricAuthority}
    {O : Fast.FastCauchyOperations A}
    {Q : Quotient.SetQuotientBackend (Fast.FastCauchyReal A) Fast._≈R_}
    (packaging : Backend.FastCauchyBackendPackaging A O)
    (operations : Quotient.FastCauchyQuotientOperations A O Q)
    (laws : Quotient.FastCauchyQuotientAlgebraLaws A O Q operations)
    (completeness : Quotient.FastCauchyQuotientCompleteness A O Q) →
  ComplexWeld.PropositionalQuotientOperationCompatibility
    (Backend.fastCauchySetoidOrderedCompleteReal O packaging)
    (Exact.fastCauchyPropositionalQuotient
      packaging operations laws completeness)
compatibilityCompiled =
  Exact.fastCauchyQuotientOperationCompatibility
