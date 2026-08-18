module DASHI.Core.ObserverIncomparabilityTypedJoinExact where

open import DASHI.Core.Prelude
import DASHI.Core.ObserverRefinementLatticeExact as Obs

record IncomparableObservers
    {State A B : Set}
    (left : Obs.Observer State A)
    (right : Obs.Observer State B) : Set where
  constructor incomparableObservers
  field
    leftCollision₁ leftCollision₂ : State
    leftSame : left leftCollision₁ ≡ left leftCollision₂
    rightSplitsLeftCollision : right leftCollision₁ ≡ right leftCollision₂ → ⊥
    rightCollision₁ rightCollision₂ : State
    rightSame : right rightCollision₁ ≡ right rightCollision₂
    leftSplitsRightCollision : left rightCollision₁ ≡ left rightCollision₂ → ⊥

open IncomparableObservers public

leftDoesNotRefineRight :
  ∀ {State A B} {left : Obs.Observer State A} {right : Obs.Observer State B} →
  IncomparableObservers left right →
  Obs.Refines right left → ⊥
leftDoesNotRefineRight witness refinement =
  rightSplitsLeftCollision witness
    (refinement
      (leftCollision₁ witness)
      (leftCollision₂ witness)
      (leftSame witness))

rightDoesNotRefineLeft :
  ∀ {State A B} {left : Obs.Observer State A} {right : Obs.Observer State B} →
  IncomparableObservers left right →
  Obs.Refines left right → ⊥
rightDoesNotRefineLeft witness refinement =
  leftSplitsRightCollision witness
    (refinement
      (rightCollision₁ witness)
      (rightCollision₂ witness)
      (rightSame witness))

jointStrictlyRefinesLeft :
  ∀ {State A B} {left : Obs.Observer State A} {right : Obs.Observer State B} →
  IncomparableObservers left right →
  Obs.StrictRefinement left (Obs.pairObserver left right)
jointStrictlyRefinesLeft {left = left} {right = right} witness =
  Obs.strictPairRefinement left right
    (leftCollision₁ witness)
    (leftCollision₂ witness)
    (leftSame witness)
    (rightSplitsLeftCollision witness)

jointStrictlyRefinesRight :
  ∀ {State A B} {left : Obs.Observer State A} {right : Obs.Observer State B} →
  IncomparableObservers left right →
  Obs.StrictRefinement right (Obs.pairObserver left right)
jointStrictlyRefinesRight {left = left} {right = right} witness =
  Obs.strictRefinement
    (Obs.pairRefinesRight left right)
    (rightCollision₁ witness)
    (rightCollision₂ witness)
    (rightSame witness)
    (λ pairSame → leftSplitsRightCollision witness (cong proj₁ pairSame))

data AutomaticSemanticMergePermission
    {State A B : Set}
    (left : Obs.Observer State A)
    (right : Obs.Observer State B) : Set where

productObservationDoesNotSelfAuthoriseSemanticMerge :
  ∀ {State A B}
    (left : Obs.Observer State A)
    (right : Obs.Observer State B) →
  AutomaticSemanticMergePermission left right → ⊥
productObservationDoesNotSelfAuthoriseSemanticMerge left right ()

record TypedObservationJoinBoundary : Set where
  constructor typedObservationJoinBoundary
  field
    incomparableObserversCanBeRetainedTogether : Bool
    jointObservationStrictlyRefinesEachWhenCrossCollisionsExist : Bool
    productObservationAutomaticallyLicensesSemanticPooling : Bool

canonicalTypedObservationJoinBoundary : TypedObservationJoinBoundary
canonicalTypedObservationJoinBoundary =
  typedObservationJoinBoundary true true false
