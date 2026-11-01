module DASHI.Programmes.RTXQuantitativeRefinementExact where

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- Quantitative refinement seam for the actual dashiRTX renderer.
--
-- The checked-in benchmark refines the worst-error quadtree leaves and then
-- re-renders.  It is therefore not an exact observation-preserving map in the
-- sense required by RTXLightTransportRefinementExact: empirical quantiles may
-- improve unevenly and some may worsen.
--
-- Rather than fake equality, the downstream consumer supplies a composable
-- error-budget relation.  Budget `n` can be read as n units of a chosen
-- per-refinement tolerance epsilon.  No metric arithmetic is baked into this
-- generic owner; an application may instantiate `Within n x y` as
-- d(x,y) <= n * epsilon.
------------------------------------------------------------------------

record QuantitativeRefinementInterface : Set₁ where
  constructor quantitativeRefinementInterface
  field
    State Observation : Set
    refine : State → State
    observe : State → Observation

    Within : Nat → Observation → Observation → Set

    withinZero :
      ∀ observation → Within zero observation observation

    withinCompose :
      ∀ {m n left middle right} →
      Within m left middle →
      Within n middle right →
      Within (m + n) left right

    oneStepBudget :
      ∀ state →
      Within (suc zero)
        (observe (refine state))
        (observe state)

open QuantitativeRefinementInterface public

refineN :
  (r : QuantitativeRefinementInterface) →
  Nat → State r → State r
refineN r zero state = state
refineN r (suc n) state = refine r (refineN r n state)

iteratedRefinementWithinDepthBudget :
  (r : QuantitativeRefinementInterface) →
  ∀ n state →
  Within r n
    (observe r (refineN r n state))
    (observe r state)
iteratedRefinementWithinDepthBudget r zero state =
  withinZero r (observe r state)
iteratedRefinementWithinDepthBudget r (suc n) state =
  withinCompose r
    (oneStepBudget r (refineN r n state))
    (iteratedRefinementWithinDepthBudget r n state)

------------------------------------------------------------------------
-- If an application can prove exact observation preservation, it may choose a
-- zero-cost relation instead.  The current benchmark evidence does not justify
-- installing that stronger instance for the real quadtree renderer.
------------------------------------------------------------------------

record RTXQuantitativeRefinementBoundary : Set where
  constructor rtxQuantitativeRefinementBoundary
  field
    benchmarkQuantileImprovementIsExactPreservation : Bool
    benchmarkQuantileImprovementIsExactPreservationIsFalse :
      benchmarkQuantileImprovementIsExactPreservation ≡ false

    perStepApproximationBudgetComposes : Bool
    perStepApproximationBudgetComposesIsTrue :
      perStepApproximationBudgetComposes ≡ true

    oneImprovedMetricForcesEveryMetricToImprove : Bool
    oneImprovedMetricForcesEveryMetricToImproveIsFalse :
      oneImprovedMetricForcesEveryMetricToImprove ≡ false

canonicalRTXQuantitativeRefinementBoundary :
  RTXQuantitativeRefinementBoundary
canonicalRTXQuantitativeRefinementBoundary =
  rtxQuantitativeRefinementBoundary
    false refl
    true refl
    false refl
