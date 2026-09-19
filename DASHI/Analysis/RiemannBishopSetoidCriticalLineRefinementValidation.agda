module DASHI.Analysis.RiemannBishopSetoidCriticalLineRefinementValidation where

open import Data.Empty using (⊥)

import Real as Bishop
import DASHI.Analysis.RiemannAnalyticSubstrate as Analytic
import DASHI.Analysis.RiemannBishopLocatedHeightCarrierExact as BishopHeight
import DASHI.Analysis.RiemannAnalyticLocatedHeightCarrierRealizationExact as Located
import DASHI.Analysis.RiemannCriticalLineStabilityRefinementExact as Stability
import DASHI.Analysis.RiemannBishopSetoidCriticalLineRefinementExact as BishopCritical

bishopEqualityDoubleNegationEliminates :
  (left right : Bishop.ℝ) →
  ((Bishop._≃_ left right → ⊥) → ⊥) →
  Bishop._≃_ left right
bishopEqualityDoubleNegationEliminates =
  BishopCritical.bishopSetoidEqualityStable

bishopCriticalCharacterizationCompilesStableRefinement :
  ∀ {analytic}
    {attachment :
      Located.AnalyticLocatedHeightCarrierAttachment
        analytic
        BishopHeight.bishopLocatedHeightCarrier} →
  BishopCritical.BishopCriticalLineHalfCharacterization analytic attachment →
  Stability.CriticalLinePredicateRefinement analytic
bishopCriticalCharacterizationCompilesStableRefinement =
  BishopCritical.compileBishopCriticalLinePredicateRefinement
