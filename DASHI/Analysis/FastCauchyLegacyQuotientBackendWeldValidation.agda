module DASHI.Analysis.FastCauchyLegacyQuotientBackendWeldValidation where

import DASHI.Analysis.FastCauchyReals as Fast
import DASHI.Analysis.FastCauchyConstructedRealBackendExact as Backend
import DASHI.Analysis.ConstructedRealBackendSpineExact as Spine
import DASHI.Analysis.FastCauchyLegacyQuotientBackendWeldExact as P

legacyQuotientWeldRegression :
  ∀ {A : Fast.RationalMetricAuthority}
    {O : Fast.FastCauchyOperations A} →
  (packaging : Backend.FastCauchyBackendPackaging A O) →
  (Q : Fast.FastCauchyQuotientRealization A O) →
  Spine.PropositionalQuotientRealization
    (Backend.fastCauchySetoidOrderedCompleteReal O packaging)
legacyQuotientWeldRegression = P.fastCauchyLegacyQuotientWeld
