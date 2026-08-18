module DASHI.Core.RecoverableObserverRefinementExact where

------------------------------------------------------------------------
-- RECOVERABLE OBSERVER REFINEMENT
--
-- A refinement ladder is especially strong when its observation maps are not
-- merely extensionally ordered, but presented as successive exact recoverable
-- projections
--
--   X -> Fine -> Coarse.
--
-- Then the existing RecoverableQuotientCompositionExact theorem says that the
-- residual of the coarse observation decomposes as the product of:
--
--   * what Fine still forgets about X, and
--   * what Coarse forgets about Fine.
--
-- This module only welds that composition theorem to the observer-refinement
-- vocabulary introduced in PR #580; it does not claim every abstract Refines
-- witness admits such a factorization.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Core.ObserverRefinementLatticeExact as Observer
import DASHI.Core.RecoverableQuotientCompositionExact as Recoverable

record RecoverableRefinementStep (State Fine Coarse : Set) : Set₁ where
  constructor recoverableRefinementStep
  field
    fineProjection : Recoverable.ExactRecoverableProjection State Fine
    coarseProjection : Recoverable.ExactRecoverableProjection Fine Coarse

open RecoverableRefinementStep public

fineObserver :
  ∀ {State Fine Coarse : Set} →
  RecoverableRefinementStep State Fine Coarse →
  Observer.Observer State Fine
fineObserver step = Recoverable.project (fineProjection step)

coarseObserver :
  ∀ {State Fine Coarse : Set} →
  RecoverableRefinementStep State Fine Coarse →
  Observer.Observer State Coarse
coarseObserver step x =
  Recoverable.project (coarseProjection step)
    (Recoverable.project (fineProjection step) x)

fineRefinesCompositeCoarse :
  ∀ {State Fine Coarse : Set}
    (step : RecoverableRefinementStep State Fine Coarse) →
  Observer.Refines (coarseObserver step) (fineObserver step)
fineRefinesCompositeCoarse step x y sameFine =
  cong (Recoverable.project (coarseProjection step)) sameFine

compositeRecoverableProjection :
  ∀ {State Fine Coarse : Set} →
  RecoverableRefinementStep State Fine Coarse →
  Recoverable.ExactRecoverableProjection State Coarse
compositeRecoverableProjection step =
  Recoverable.composeRecoverable
    (fineProjection step)
    (coarseProjection step)

compositeResidualDecomposes :
  ∀ {State Fine Coarse : Set}
    (step : RecoverableRefinementStep State Fine Coarse) →
  Recoverable.Residual (compositeRecoverableProjection step)
  ≡
  (Recoverable.Residual (fineProjection step)
    × Recoverable.Residual (coarseProjection step))
compositeResidualDecomposes step =
  Recoverable.compositeResidualIsProduct
    (fineProjection step)
    (coarseProjection step)

record RecoverableObserverRefinementBoundary : Set where
  constructor recoverableObserverRefinementBoundary
  field
    successiveRecoverableProjectionGivesStaticRefinement : Bool
    successiveRecoverableProjectionGivesStaticRefinementIsTrue :
      successiveRecoverableProjectionGivesStaticRefinement ≡ true
    compositeResidualIsProductOfStageResiduals : Bool
    compositeResidualIsProductOfStageResidualsIsTrue :
      compositeResidualIsProductOfStageResiduals ≡ true
    arbitraryRefinesWitnessAutomaticallyRecoverable : Bool
    arbitraryRefinesWitnessAutomaticallyRecoverableIsFalse :
      arbitraryRefinesWitnessAutomaticallyRecoverable ≡ false

canonicalRecoverableObserverRefinementBoundary :
  RecoverableObserverRefinementBoundary
canonicalRecoverableObserverRefinementBoundary =
  recoverableObserverRefinementBoundary true refl true refl false refl
