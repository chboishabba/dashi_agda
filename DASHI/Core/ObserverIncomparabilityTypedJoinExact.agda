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

------------------------------------------------------------------------
-- Least common refinement / join universal property.
--
-- If a third observer is fine enough to refine BOTH transverse observers,
-- equality under that third observer implies equality of the pair.  Therefore
-- the typed pair observer is the least common refinement in the observational
-- information preorder; this is stronger than merely showing that adding the
-- second coordinate gives a strict refinement.
------------------------------------------------------------------------

jointLeastCommonRefinement :
  ∀ {State A B Common}
    (left : Obs.Observer State A)
    (right : Obs.Observer State B)
    (common : Obs.Observer State Common) →
  Obs.Refines left common →
  Obs.Refines right common →
  Obs.Refines (Obs.pairObserver left right) common
jointLeastCommonRefinement left right common commonRefinesLeft commonRefinesRight x y sameCommon =
  cong₂ _,_
    (commonRefinesLeft x y sameCommon)
    (commonRefinesRight x y sameCommon)

record LeastTypedObservationJoin
    {State A B : Set}
    (left : Obs.Observer State A)
    (right : Obs.Observer State B) : Set₁ where
  constructor leastTypedObservationJoin
  field
    join : Obs.Observer State (A × B)
    joinRefinesLeft : Obs.Refines left join
    joinRefinesRight : Obs.Refines right join
    leastCommonRefinement :
      ∀ {Common : Set}
        (common : Obs.Observer State Common) →
      Obs.Refines left common →
      Obs.Refines right common →
      Obs.Refines join common

open LeastTypedObservationJoin public

canonicalLeastTypedObservationJoin :
  ∀ {State A B}
    (left : Obs.Observer State A)
    (right : Obs.Observer State B) →
  LeastTypedObservationJoin left right
canonicalLeastTypedObservationJoin left right =
  leastTypedObservationJoin
    (Obs.pairObserver left right)
    (Obs.pairRefinesLeft left right)
    (Obs.pairRefinesRight left right)
    (jointLeastCommonRefinement left right)

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
    pairObserverHasLeastCommonRefinementProperty : Bool
    productObservationAutomaticallyLicensesSemanticPooling : Bool
    leastJoinAutomaticallySeparatesWholeState : Bool

canonicalTypedObservationJoinBoundary : TypedObservationJoinBoundary
canonicalTypedObservationJoinBoundary =
  typedObservationJoinBoundary true true true false false
