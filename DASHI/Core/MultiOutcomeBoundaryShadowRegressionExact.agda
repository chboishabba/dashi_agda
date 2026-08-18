module DASHI.Core.MultiOutcomeBoundaryShadowRegressionExact where

------------------------------------------------------------------------
-- MULTI-OUTCOME OBSERVATION: INFORMATIVE SHADOWS NEED NOT RECONSTRUCT
--
-- This finite carrier is deliberately abstract.  It demonstrates the theorem
-- shape needed for policy/evaluation work without assigning empirical values
-- to any real programme.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Core.BoundaryObservationReconstructionExact as Boundary
import DASHI.Core.ObserverRefinementLatticeExact as Observer

OutcomeState : Set
OutcomeState = Bool × (Bool × Bool)

employmentObserver : Observer.Observer OutcomeState Bool
employmentObserver = proj₁

childOutcomeObserver : Observer.Observer OutcomeState Bool
childOutcomeObserver state = proj₁ (proj₂ state)

fiscalObserver : Observer.Observer OutcomeState Bool
fiscalObserver state = proj₂ (proj₂ state)

employmentChildObserver :
  Observer.Observer OutcomeState (Bool × Bool)
employmentChildObserver =
  Observer.pairObserver employmentObserver childOutcomeObserver

fullOutcomeObserver : Observer.Observer OutcomeState OutcomeState
fullOutcomeObserver state = state

employmentLeft employmentRight : OutcomeState
employmentLeft = false , (false , false)
employmentRight = false , (true , false)

employmentCollision : Observer.ObserverCollision employmentObserver
employmentCollision =
  Observer.observerCollision
    employmentLeft
    employmentRight
    refl
    (λ same → falseNotTrue (cong childOutcomeObserver same))
  where
    falseNotTrue : false ≡ true → ⊥
    falseNotTrue ()

employmentChildLeft employmentChildRight : OutcomeState
employmentChildLeft = false , (false , false)
employmentChildRight = false , (false , true)

employmentChildCollision :
  Observer.ObserverCollision employmentChildObserver
employmentChildCollision =
  Observer.observerCollision
    employmentChildLeft
    employmentChildRight
    refl
    (λ same → falseNotTrue (cong fiscalObserver same))
  where
    falseNotTrue : false ≡ true → ⊥
    falseNotTrue ()

employmentCannotReconstructWholeOutcomeState :
  Boundary.ExactBoundaryReconstruction employmentObserver → ⊥
employmentCannotReconstructWholeOutcomeState =
  Boundary.collisionBlocksExactBoundaryReconstruction employmentCollision

employmentPlusChildStillCannotReconstructWholeOutcomeState :
  Boundary.ExactBoundaryReconstruction employmentChildObserver → ⊥
employmentPlusChildStillCannotReconstructWholeOutcomeState =
  Boundary.collisionBlocksExactBoundaryReconstruction employmentChildCollision

fullOutcomeVectorReconstructsExactly :
  Boundary.ExactBoundaryReconstruction fullOutcomeObserver
fullOutcomeVectorReconstructsExactly =
  Boundary.exactBoundaryReconstruction (λ state → state) (λ state → refl)

record MultiOutcomeBoundaryShadowBoundary : Set where
  constructor multiOutcomeBoundaryShadowBoundary
  field
    oneOutcomeAutomaticallyReconstructsWholeState : Bool
    oneOutcomeAutomaticallyReconstructsWholeStateIsFalse :
      oneOutcomeAutomaticallyReconstructsWholeState ≡ false
    addingAnotherOutcomeAutomaticallyReconstructsWholeState : Bool
    addingAnotherOutcomeAutomaticallyReconstructsWholeStateIsFalse :
      addingAnotherOutcomeAutomaticallyReconstructsWholeState ≡ false
    declaredFullVectorCanBeReconstructiveWhenProved : Bool
    declaredFullVectorCanBeReconstructiveWhenProvedIsTrue :
      declaredFullVectorCanBeReconstructiveWhenProved ≡ true

canonicalMultiOutcomeBoundaryShadowBoundary :
  MultiOutcomeBoundaryShadowBoundary
canonicalMultiOutcomeBoundaryShadowBoundary =
  multiOutcomeBoundaryShadowBoundary false refl false refl true refl
