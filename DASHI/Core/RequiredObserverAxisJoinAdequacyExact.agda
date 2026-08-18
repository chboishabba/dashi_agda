module DASHI.Core.RequiredObserverAxisJoinAdequacyExact where

------------------------------------------------------------------------
-- REQUIRED OBSERVER AXES AND JOINT ADEQUACY
--
-- QueryIndexedProjectionAdequacyExact already establishes that adequacy is
-- query-relative, not an intrinsic Boolean property of a projection.
-- IntersectionalNonFactorability already owns the exact factorisation carrier.
--
-- This module adds only the product law needed by transverse observers:
-- if a candidate projection retains two required observation axes separately,
-- it retains their joint pair; if either required axis has a fibre collision
-- split by that axis, the candidate cannot claim to retain both.
--
-- The result is deliberately not a world-completeness theorem.  A consumer may
-- require one axis, another axis, or both; the relevant joint carrier is indexed
-- by that declared requirement.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
import DASHI.Core.IntersectionalNonFactorability as NonFactor
import DASHI.Core.QueryIndexedProjectionAdequacyExact as Query

RetainsAxis :
  ∀ {State Observation Axis : Set} →
  (State → Observation) →
  (State → Axis) →
  Set₁
RetainsAxis candidate axis = NonFactor.FactorsThrough candidate axis

jointAxis :
  ∀ {State A B : Set} →
  (State → A) →
  (State → B) →
  State → A × B
jointAxis left right state = left state , right state

candidateRetainingBothRetainsJoint :
  ∀ {State Observation A B : Set}
    {candidate : State → Observation}
    {left : State → A}
    {right : State → B} →
  RetainsAxis candidate left →
  RetainsAxis candidate right →
  RetainsAxis candidate (jointAxis left right)
candidateRetainingBothRetainsJoint leftFactor rightFactor =
  NonFactor.factorsThrough
    (λ observation →
      NonFactor.interpretFlat leftFactor observation ,
      NonFactor.interpretFlat rightFactor observation)
    (λ state →
      cong₂ _,_
        (NonFactor.factorisation leftFactor state)
        (NonFactor.factorisation rightFactor state))

jointRetainsLeft :
  ∀ {State A B : Set}
    (left : State → A)
    (right : State → B) →
  RetainsAxis (jointAxis left right) left
jointRetainsLeft left right =
  NonFactor.factorsThrough proj₁ (λ state → refl)

jointRetainsRight :
  ∀ {State A B : Set}
    (left : State → A)
    (right : State → B) →
  RetainsAxis (jointAxis left right) right
jointRetainsRight left right =
  NonFactor.factorsThrough proj₂ (λ state → refl)

record RetainsBothRequiredAxes
    {State Observation A B : Set}
    (candidate : State → Observation)
    (left : State → A)
    (right : State → B) : Set₁ where
  constructor retainsBothRequiredAxes
  field
    retainsLeft : RetainsAxis candidate left
    retainsRight : RetainsAxis candidate right

open RetainsBothRequiredAxes public

retainsBothGivesJointFactorisation :
  ∀ {State Observation A B : Set}
    {candidate : State → Observation}
    {left : State → A}
    {right : State → B} →
  RetainsBothRequiredAxes candidate left right →
  RetainsAxis candidate (jointAxis left right)
retainsBothGivesJointFactorisation retained =
  candidateRetainingBothRetainsJoint
    (retainsLeft retained)
    (retainsRight retained)

leftAxisDefectBlocksRetainingBoth :
  ∀ {State Observation A B : Set}
    {candidate : State → Observation}
    {left : State → A}
    {right : State → B} →
  NonFactor.NonFactorabilityWitness candidate left →
  RetainsBothRequiredAxes candidate left right →
  ⊥
leftAxisDefectBlocksRetainingBoth defect retained =
  NonFactor.witnessRulesOutEveryFlatFactorisation defect (retainsLeft retained)

rightAxisDefectBlocksRetainingBoth :
  ∀ {State Observation A B : Set}
    {candidate : State → Observation}
    {left : State → A}
    {right : State → B} →
  NonFactor.NonFactorabilityWitness candidate right →
  RetainsBothRequiredAxes candidate left right →
  ⊥
rightAxisDefectBlocksRetainingBoth defect retained =
  NonFactor.witnessRulesOutEveryFlatFactorisation defect (retainsRight retained)

------------------------------------------------------------------------
-- Query-indexed finite witness.
--
-- The same pair observation answers each coordinate query exactly.  This is a
-- concrete specialization of query-relative adequacy, not a claim that the
-- pair is adequate for every possible query on the fine state.
------------------------------------------------------------------------

data DemoState : Set where demo00 demo01 demo10 demo11 : DemoState
data LeftAxis : Set where left0 left1 : LeftAxis
data RightAxis : Set where right0 right1 : RightAxis
data AxisQuery : Set where askLeft askRight : AxisQuery
data AxisAnswer : Set where
  leftAnswer0 leftAnswer1 rightAnswer0 rightAnswer1 : AxisAnswer

leftDemo : DemoState → LeftAxis
leftDemo demo00 = left0
leftDemo demo01 = left0
leftDemo demo10 = left1
leftDemo demo11 = left1

rightDemo : DemoState → RightAxis
rightDemo demo00 = right0
rightDemo demo01 = right1
rightDemo demo10 = right0
rightDemo demo11 = right1

answerDemo : AxisQuery → DemoState → AxisAnswer
answerDemo askLeft demo00 = leftAnswer0
answerDemo askLeft demo01 = leftAnswer0
answerDemo askLeft demo10 = leftAnswer1
answerDemo askLeft demo11 = leftAnswer1
answerDemo askRight demo00 = rightAnswer0
answerDemo askRight demo01 = rightAnswer1
answerDemo askRight demo10 = rightAnswer0
answerDemo askRight demo11 = rightAnswer1

demoSemantics : Query.QuerySemantics DemoState AxisQuery AxisAnswer
demoSemantics = Query.querySemantics answerDemo

pairDemo : DemoState → LeftAxis × RightAxis
pairDemo = jointAxis leftDemo rightDemo

pairAdequateForLeftQuery : Query.AdequateFor pairDemo demoSemantics askLeft
pairAdequateForLeftQuery =
  Query.factorsForQuery
    (λ { (left0 , right) → leftAnswer0
       ; (left1 , right) → leftAnswer1 })
    (λ { demo00 → refl
       ; demo01 → refl
       ; demo10 → refl
       ; demo11 → refl })

pairAdequateForRightQuery : Query.AdequateFor pairDemo demoSemantics askRight
pairAdequateForRightQuery =
  Query.factorsForQuery
    (λ { (left , right0) → rightAnswer0
       ; (left , right1) → rightAnswer1 })
    (λ { demo00 → refl
       ; demo01 → refl
       ; demo10 → refl
       ; demo11 → refl })

record RequiredObserverAxisJoinBoundary : Set where
  field
    requiredAxesMustBeRetainedRelativeToConsumer : Bool
    carryingBothAxesConstructsJointFactorisation : Bool
    missingOneAxisCanBeCompensatedByStrongOtherAxis : Bool
    jointAdequacyForDeclaredAxesMeansWorldCompleteness : Bool

canonicalRequiredObserverAxisJoinBoundary :
  RequiredObserverAxisJoinBoundary
canonicalRequiredObserverAxisJoinBoundary = record
  { requiredAxesMustBeRetainedRelativeToConsumer = true
  ; carryingBothAxesConstructsJointFactorisation = true
  ; missingOneAxisCanBeCompensatedByStrongOtherAxis = false
  ; jointAdequacyForDeclaredAxesMeansWorldCompleteness = false
  }
