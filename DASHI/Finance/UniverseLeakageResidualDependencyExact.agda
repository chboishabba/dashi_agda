module DASHI.Finance.UniverseLeakageResidualDependencyExact where

open import DASHI.Core.Prelude

import DASHI.Core.ObserverRefinementLatticeExact as Observer
import DASHI.Core.ResidualObserverDependencyExact as Residual

------------------------------------------------------------------------
-- Cross-pollination: universe leakage is not only an illegal temporal
-- transport.  It is also an action-relevant hidden residual dependency that a
-- coarse feature observer can quotient away.
------------------------------------------------------------------------

data BacktestState : Set where
  dynamicHistoricalUniverse : BacktestState
  leakedStaticFutureUniverse : BacktestState

data BacktestAction : Set where
  evaluateStrategy : BacktestAction

data UniverseDependencyCode : Set where
  universePIT : UniverseDependencyCode
  universeFutureDependent : UniverseDependencyCode

data AssetIndex : Set where
  assetIndex : AssetIndex

data CoarseFeatureCode : Set where
  sameCausalFeatureSurface : CoarseFeatureCode

coarseFeatureObserver : Observer.Observer BacktestState CoarseFeatureCode
coarseFeatureObserver dynamicHistoricalUniverse = sameCausalFeatureSurface
coarseFeatureObserver leakedStaticFutureUniverse = sameCausalFeatureSurface

universeDependency :
  Residual.ResidualDependencyObserver
    BacktestState BacktestAction AssetIndex UniverseDependencyCode
universeDependency = record
  { Influences = λ _ _ _ _ → ⊤
  ; dependencyCode = dependencyCodeLocal
  }
  where
    dependencyCodeLocal : BacktestState → BacktestAction → UniverseDependencyCode
    dependencyCodeLocal dynamicHistoricalUniverse evaluateStrategy = universePIT
    dependencyCodeLocal leakedStaticFutureUniverse evaluateStrategy = universeFutureDependent

pitCodeNotFutureCode : universePIT ≡ universeFutureDependent → ⊥
pitCodeNotFutureCode ()

staticUniverseLeakageHiddenDependency :
  Residual.HiddenResidualDependency
    universeDependency
    coarseFeatureObserver
    evaluateStrategy
staticUniverseLeakageHiddenDependency =
  Residual.hiddenResidualDependency
    dynamicHistoricalUniverse
    leakedStaticFutureUniverse
    refl
    pitCodeNotFutureCode

universeDependencyStrictlyRefinesFeatures :
  Observer.StrictRefinement
    coarseFeatureObserver
    (Residual.refinedObservationAt
      universeDependency
      coarseFeatureObserver
      evaluateStrategy)
universeDependencyStrictlyRefinesFeatures =
  Residual.hiddenResidualDependencyGivesStrictRefinement
    staticUniverseLeakageHiddenDependency

universeDependencyCannotDescendToFeatures :
  Residual.DependencyCodeDescendsAt
    universeDependency
    coarseFeatureObserver
    evaluateStrategy →
  ⊥
universeDependencyCannotDescendToFeatures =
  Residual.hiddenResidualDependencyBlocksDescent
    staticUniverseLeakageHiddenDependency

------------------------------------------------------------------------
-- Interpretation: two backtests can expose the same causal feature surface
-- yet differ in future-universe dependence.  Therefore feature-level equality
-- is insufficient to certify PIT backtest identity.
------------------------------------------------------------------------

record UniverseDependencyBoundary : Set where
  constructor universeDependencyBoundary
  field
    sameFeatureSurfaceImpliesSameUniverseDependency : Bool
    sameFeatureSurfaceImpliesSameUniverseDependencyIsFalse :
      sameFeatureSurfaceImpliesSameUniverseDependency ≡ false
    hiddenUniverseDependencyBlocksCoarseDescent : Bool
    hiddenUniverseDependencyBlocksCoarseDescentIsTrue :
      hiddenUniverseDependencyBlocksCoarseDescent ≡ true

canonicalUniverseDependencyBoundary : UniverseDependencyBoundary
canonicalUniverseDependencyBoundary =
  universeDependencyBoundary false refl true refl
