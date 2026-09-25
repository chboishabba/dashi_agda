module DASHI.Mathematics.Complexity.PNotEqualsNPQ1ReachableStateRecurrenceExact where

------------------------------------------------------------------------
-- Q1 AT EVERY LIVE STATE -> THE ACTUAL TOTAL Q2 STEP SYSTEM
--
-- The live Clay target is not merely a root quotient.  Q2 needs a total
-- transition whose every successful step decreases the whole recursive state.
--
-- This owner makes that recurrence executable.
--
-- A per-state Q1 constructor returns either nothing (terminal) or a closed
-- quotient plus its all-overhead strict-fit certificate.
--
-- From that data we construct the actual next Q2 state by replacing the
-- current Cook formula with the closed quotient authority while preserving
-- program-code size, rebinding overhead, and the resource-budget ceiling.
--
-- No SAT truth is inspected here.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Nat.Base using (_≤_; _<_)
import Data.Nat.Properties as NatP
open import Data.Product using (Σ; _,_)
open import Relation.Binary.PropositionalEquality using (subst)

import DASHI.Mathematics.Complexity.CookLevinCircuitGCTBoundary as Cook
import DASHI.Mathematics.Complexity.BooleanFormulaSATSelfReductionExact as SAT
import DASHI.Mathematics.Complexity.PNotEqualsNPCookIndexedFormulaBridgeExact as Bridge
import DASHI.Mathematics.Complexity.PNotEqualsNPProgramDescriptionFormulaEmbeddingExact as Size
import DASHI.Mathematics.Complexity.PNotEqualsNPClosedStrictRepresentativeQuotientExact as Closed
import DASHI.Mathematics.Complexity.PNotEqualsNPClosedRestrictionQuotientSATAuthorityExact as Authority
import DASHI.Mathematics.Complexity.PNotEqualsNPSelfReferenceAllOverheadBudgetExact as Q1
import DASHI.Mathematics.Complexity.PNotEqualsNPBoundedSelfReferenceWellFoundedExact as Q2

------------------------------------------------------------------------
-- The exact overhead associated with one live Q2 state.
------------------------------------------------------------------------

stateOverhead :
  Q2.BoundedSelfReferenceState →
  Q1.SelfReferenceOverhead
stateOverhead state =
  Q1.self-reference-overhead
    (Q2.programCodeSize state)
    (Q2.rebindingOverhead state)

------------------------------------------------------------------------
-- One constructive Q1 witness at one state.
------------------------------------------------------------------------

Q1StateWitness :
  (state : Q2.BoundedSelfReferenceState) →
  Set₁
Q1StateWitness state =
  Σ
    (Closed.ClosedStrictRepresentativeQuotient
      (Bridge.cookToIndexed
        (Q2.currentFormula state)))
    (λ closed →
      Q1.ClosedQuotientAllOverheadFits
        closed
        (stateOverhead state))

Q1StateConstructor : Set₁
Q1StateConstructor =
  (state : Q2.BoundedSelfReferenceState) →
  Maybe (Q1StateWitness state)

------------------------------------------------------------------------
-- One actual next state.
------------------------------------------------------------------------

q1AuthorityNextState :
  (state : Q2.BoundedSelfReferenceState) →
  (closed :
    Closed.ClosedStrictRepresentativeQuotient
      (Bridge.cookToIndexed
        (Q2.currentFormula state))) →
  (fits :
    Q1.ClosedQuotientAllOverheadFits
      closed
      (stateOverhead state)) →
  Q2.BoundedSelfReferenceState
q1AuthorityNextState
    state
    closed
    fits =
  Q2.bounded-self-reference-state
    (Authority.closedQuotientSATAuthority closed)
    (Q2.programCodeSize state)
    (Q2.rebindingOverhead state)
    (Q2.resourceBudget state)
    nextFitsBudget
  where
    authorityPayloadBelowCurrentFormula :
      Size.formulaNodeCount
          (Authority.closedQuotientSATAuthority closed)
        + Q1.totalOverhead (stateOverhead state)
      <
      Size.formulaNodeCount
        (Q2.currentFormula state)
    authorityPayloadBelowCurrentFormula
      rewrite
        Bridge.indexedAfterCook
          (Q2.currentFormula state) =
      Q1.closedAuthorityPlusAllOverheadStrictlySmaller
        closed
        (stateOverhead state)
        fits

    authorityPayloadFitsCurrentMeasure :
      Size.formulaNodeCount
          (Authority.closedQuotientSATAuthority closed)
        + Q1.totalOverhead (stateOverhead state)
      ≤
      Q2.recursiveMeasure state
    authorityPayloadFitsCurrentMeasure =
      NatP.≤-trans
        (NatP.<⇒≤
          authorityPayloadBelowCurrentFormula)
        (NatP.m≤m+n
          (Size.formulaNodeCount
            (Q2.currentFormula state))
          (Q1.totalOverhead
            (stateOverhead state)))

    nextFitsBudget :
      Size.formulaNodeCount
          (Authority.closedQuotientSATAuthority closed)
        +
        (Q2.programCodeSize state
          + Q2.rebindingOverhead state)
      ≤
      Q2.resourceBudget state
    nextFitsBudget =
      NatP.≤-trans
        authorityPayloadFitsCurrentMeasure
        (Q2.stateFitsBudget state)

------------------------------------------------------------------------
-- Whole-state measure decrease.
------------------------------------------------------------------------

q1AuthorityNextStateStrictlyDecreases :
  (state : Q2.BoundedSelfReferenceState) →
  (closed :
    Closed.ClosedStrictRepresentativeQuotient
      (Bridge.cookToIndexed
        (Q2.currentFormula state))) →
  (fits :
    Q1.ClosedQuotientAllOverheadFits
      closed
      (stateOverhead state)) →
  Q2.recursiveMeasure
    (q1AuthorityNextState
      state
      closed
      fits)
  <
  Q2.recursiveMeasure state
q1AuthorityNextStateStrictlyDecreases
    state
    closed
    fits =
  NatP.<-≤-trans
    payloadBelowCurrentFormula
    currentFormulaBelowMeasure
  where
    payloadBelowCurrentFormula :
      Q2.recursiveMeasure
        (q1AuthorityNextState
          state
          closed
          fits)
      <
      Size.formulaNodeCount
        (Q2.currentFormula state)
    payloadBelowCurrentFormula
      rewrite
        Bridge.indexedAfterCook
          (Q2.currentFormula state) =
      Q1.closedAuthorityPlusAllOverheadStrictlySmaller
        closed
        (stateOverhead state)
        fits

    currentFormulaBelowMeasure :
      Size.formulaNodeCount
        (Q2.currentFormula state)
      ≤
      Q2.recursiveMeasure state
    currentFormulaBelowMeasure =
      NatP.m≤m+n
        (Size.formulaNodeCount
          (Q2.currentFormula state))
        (Q1.totalOverhead
          (stateOverhead state))

------------------------------------------------------------------------
-- Computed Maybe transition.
------------------------------------------------------------------------

q1Next :
  Q1StateConstructor →
  Q2.BoundedSelfReferenceState →
  Maybe Q2.BoundedSelfReferenceState
q1Next constructor state
    with constructor state
... | nothing =
  nothing
... | just (closed , fits) =
  just
    (q1AuthorityNextState
      state
      closed
      fits)

justInjective :
  ∀ {A : Set} {left right : A} →
  just left ≡ just right →
  left ≡ right
justInjective refl =
  refl

q1NextStrictlyDecreases :
  (constructor : Q1StateConstructor) →
  (state nextState : Q2.BoundedSelfReferenceState) →
  q1Next constructor state
  ≡
  just nextState →
  Q2.recursiveMeasure nextState
  <
  Q2.recursiveMeasure state
q1NextStrictlyDecreases
    constructor
    state
    nextState
    nextEquation
    with constructor state
... | nothing =
  caseNothing nextEquation
  where
    caseNothing :
      nothing ≡ just nextState →
      Q2.recursiveMeasure nextState
      <
      Q2.recursiveMeasure state
    caseNothing ()
... | just (closed , fits) =
  subst
    (λ target →
      Q2.recursiveMeasure target
      <
      Q2.recursiveMeasure state)
    (justInjective nextEquation)
    (q1AuthorityNextStateStrictlyDecreases
      state
      closed
      fits)

------------------------------------------------------------------------
-- Q1 recurrence automatically gives the Q2 step system.
------------------------------------------------------------------------

q1ConstructorToQ2StepSystem :
  Q1StateConstructor →
  Q2.BoundedSelfReferenceStepSystem
q1ConstructorToQ2StepSystem constructor =
  Q2.bounded-self-reference-step-system
    (q1Next constructor)
    (q1NextStrictlyDecreases constructor)

------------------------------------------------------------------------
-- CONSEQUENCE
--
-- Building the total Q2 recursion is no longer a separate theorem.
--
-- The only live recursive construction premise is:
--
--   state -> Maybe (closed quotient + all-overhead strict-fit proof).
--
-- Every successful branch contains the actual Q1 witness for THAT state.  The
-- Q2 transition and well-foundedness proof are compiled automatically.
------------------------------------------------------------------------
