module DASHI.Cognition.PNF.ResidualSamplingObserverRepairExact where

------------------------------------------------------------------------
-- STATIC QUERY SUFFICIENCY IS NOT DYNAMIC SAFETY -- BUT THE RETAINED
-- RESIDUAL GIVES THE SOURCE-NATIVE REFINEMENT THAT REPAIRS THIS EXAMPLE.
--
-- SemanticSamplingDynamicSafety already proves that the visible Boolean is a
-- sufficient current-query observation while the same projection is future-
-- unsafe: an admissible action can expose the retained residual.  We now use
-- ObserverRefinementLatticeExact to make that residual the next observer
-- coordinate rather than replacing the counterexample with an unrelated full
-- state.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Cognition.PNF.SemanticSamplingDynamicSafety as Sampling
import DASHI.Cognition.PNF.SemanticSamplingLookupGeometry as Lookup
import DASHI.Cognition.PNF.TerminalisationDefectRegression as Regression
import DASHI.Core.DynamicalQuotientSafety as Dynamic
import DASHI.Core.FutureObservationLanguageQuotientExact as Future
import DASHI.Core.ObserverFactorizedRefinementExact as Factorized
import DASHI.Core.ObserverRefinementFutureSafetyExact as FutureSafety
import DASHI.Core.ObserverRefinementLatticeExact as Observer

residualBitObserver : Observer.Observer Regression.ResidualState Bool
residualBitObserver = proj₂

visibleResidualObserver :
  Observer.Observer Regression.ResidualState (Bool × Bool)
visibleResidualObserver =
  Observer.pairObserver Regression.residualProjection residualBitObserver

visibleResidualStrictlyRefinesVisible :
  Observer.StrictRefinement
    Regression.residualProjection
    visibleResidualObserver
visibleResidualStrictlyRefinesVisible =
  Observer.strictPairRefinement
    Regression.residualProjection
    residualBitObserver
    (false , true)
    (false , false)
    refl
    Regression.trueNotFalse

visibleFactorsThroughVisibleResidual :
  Factorized.FactorizedRefinement
    Regression.residualProjection
    visibleResidualObserver
visibleFactorsThroughVisibleResidual =
  Factorized.pairObserverFactorsToLeft
    Regression.residualProjection
    residualBitObserver

visibleResidualSeparatesResidualState :
  Observer.Separating visibleResidualObserver
visibleResidualSeparatesResidualState
  (leftVisible , leftResidual)
  (rightVisible , rightResidual)
  same
  with cong proj₁ same | cong proj₂ same
... | refl | refl = refl

visibleResidualIsFutureLanguageSafe :
  Future.FutureLanguageSafeProjection
    Regression.residualSystem
    Regression.residualProjection
    visibleResidualObserver
visibleResidualIsFutureLanguageSafe =
  FutureSafety.separatingObserverIsFutureLanguageSafe
    visibleResidualSeparatesResidualState

------------------------------------------------------------------------
-- Keep the original negative theorem visible: current-query sufficiency of
-- the coarse projection coexists with its dynamic defect.
------------------------------------------------------------------------

coarseCurrentQueryStillSufficient :
  Lookup.QuerySufficiency Sampling.residualSamplingTower zero Bool
coarseCurrentQueryStillSufficient = Sampling.staticResidualQuerySufficiency

coarseProjectionStillFutureUnsafe :
  Dynamic.DynamicConsumerSafety
    Regression.residualSystem
    Regression.residualProjection →
  ⊥
coarseProjectionStillFutureUnsafe =
  Sampling.staticQuerySufficiencyDoesNotSupplyDynamicSafety

record ResidualSamplingObserverRepairBoundary : Set where
  constructor residualSamplingObserverRepairBoundary
  field
    coarseCurrentQuerySufficiencyRetained : Bool
    coarseCurrentQuerySufficiencyRetainedIsTrue :
      coarseCurrentQuerySufficiencyRetained ≡ true
    coarseStillFutureUnsafe : Bool
    coarseStillFutureUnsafeIsTrue : coarseStillFutureUnsafe ≡ true
    residualIsStrictSourceNativeRefinement : Bool
    residualIsStrictSourceNativeRefinementIsTrue :
      residualIsStrictSourceNativeRefinement ≡ true
    refinedObserverFutureSafe : Bool
    refinedObserverFutureSafeIsTrue : refinedObserverFutureSafe ≡ true

canonicalResidualSamplingObserverRepairBoundary :
  ResidualSamplingObserverRepairBoundary
canonicalResidualSamplingObserverRepairBoundary =
  residualSamplingObserverRepairBoundary true refl true refl true refl true refl
