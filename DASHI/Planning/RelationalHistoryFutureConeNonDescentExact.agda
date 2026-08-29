module DASHI.Planning.RelationalHistoryFutureConeNonDescentExact where

open import DASHI.Core.Prelude
import DASHI.Core.IntersectionalNonFactorability as INF

------------------------------------------------------------------------
-- RELATIONAL HISTORY -> FUTURE-CONE NON-DESCENT
------------------------------------------------------------------------

data SituatedHistoryState : Set where
  samePresentContinuousRelation samePresentDisruptedRelation : SituatedHistoryState

data PresentPlanningView : Set where
  samePresentSurface : PresentPlanningView

data FutureConeCode : Set where
  continuityPreservingCone repairRequiredCone : FutureConeCode

presentObserver : SituatedHistoryState → PresentPlanningView
presentObserver samePresentContinuousRelation = samePresentSurface
presentObserver samePresentDisruptedRelation = samePresentSurface

futureConeConsumer : SituatedHistoryState → FutureConeCode
futureConeConsumer samePresentContinuousRelation = continuityPreservingCone
futureConeConsumer samePresentDisruptedRelation = repairRequiredCone

futureConeDiffers :
  futureConeConsumer samePresentContinuousRelation ≡
  futureConeConsumer samePresentDisruptedRelation → ⊥
futureConeDiffers ()

relationalHistoryWitness :
  INF.NonFactorabilityWitness presentObserver futureConeConsumer
relationalHistoryWitness =
  INF.nonFactorabilityWitness
    samePresentContinuousRelation
    samePresentDisruptedRelation
    refl
    futureConeDiffers

presentOnlyPlanningCannotDetermineFutureCone :
  INF.FactorsThrough presentObserver futureConeConsumer → ⊥
presentOnlyPlanningCannotDetermineFutureCone =
  INF.witnessRulesOutEveryFlatFactorisation relationalHistoryWitness

presentRechartingCannotRecoverRelationalFutureCone :
  ∀ {Recharted : Set} →
  (rechart : PresentPlanningView → Recharted) →
  INF.FactorsThrough (λ s → rechart (presentObserver s)) futureConeConsumer → ⊥
presentRechartingCannotRecoverRelationalFutureCone rechart =
  INF.rechartingCannotRecoverErasedPhenomenon rechart relationalHistoryWitness
