module DASHI.Mathematics.Complexity.PNotEqualsNPQ1OperationalConstructionCostExact where

------------------------------------------------------------------------
-- Q1 COST SEMANTICS: CONSTRUCTION COST IS DERIVED FROM OUTPUT EMISSION
--
-- The previous construction-charged owner charges a Nat, but that Nat is still
-- supplied independently of an execution object.
--
-- This owner removes that freedom on the live route.
--
-- A successful construction run carries:
--
--   * the actual Q1 witness;
--   * one emitted cell for every quotient state;
--   * an auxiliary execution trace for all remaining constructor work.
--
-- Its cost is DEFINED as:
--
--   stateCount + length auxiliaryTrace.
--
-- Therefore every successful constructor pays at least one unit for every
-- quotient state before representative-chain/classifier work is counted.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; _+_)
open import Agda.Builtin.Unit using (⊤)
open import Data.List.Base using (List; length)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Nat.Base using (_≤_; _<_)
import Data.Nat.Properties as NatP
open import Data.Product using (proj₁)
open import Data.Vec.Base using (Vec)

import DASHI.Mathematics.Complexity.PNotEqualsNPBoundedSelfReferenceWellFoundedExact as Q2
import DASHI.Mathematics.Complexity.PNotEqualsNPQ1ReachableStateRecurrenceExact as Recurrence
import DASHI.Mathematics.Complexity.PNotEqualsNPQ1ConstructionChargedRecurrenceExact as Charged
import DASHI.Mathematics.Complexity.PNotEqualsNPClosedStrictRepresentativeQuotientExact as Closed
import DASHI.Mathematics.Complexity.PNotEqualsNPStrictSemanticRepresentativeQuotientExact as Strict
import DASHI.Mathematics.Complexity.PNotEqualsNPResourceClosingRestrictionQuotientExact as Quotient

------------------------------------------------------------------------
-- State count of the actual closed quotient carried by one Q1 witness.
------------------------------------------------------------------------

q1WitnessStateCount :
  ∀ {state : Q2.BoundedSelfReferenceState} →
  Recurrence.Q1StateWitness state →
  Nat
q1WitnessStateCount witness =
  Quotient.stateCount
    (Strict.quotient
      (Closed.strictQuotient
        (proj₁ witness)))

------------------------------------------------------------------------
-- Normalized constructor execution receipt.
------------------------------------------------------------------------

record OperationalQ1ConstructionRun
    (state : Q2.BoundedSelfReferenceState) : Set₁ where
  constructor operational-q1-construction-run
  field
    q1Witness :
      Recurrence.Q1StateWitness state

    emittedStateCells :
      Vec ⊤ (q1WitnessStateCount q1Witness)

    auxiliaryTrace :
      List ⊤

    operationalAndNextStrict :
      (q1WitnessStateCount q1Witness + length auxiliaryTrace)
        +
      Q2.recursiveMeasure
        (Charged.q1WitnessNextState state q1Witness)
      <
      Q2.recursiveMeasure state

open OperationalQ1ConstructionRun public

------------------------------------------------------------------------
-- Derived cost: there is no independent Nat field.
------------------------------------------------------------------------

runConstructionCost :
  ∀ {state : Q2.BoundedSelfReferenceState} →
  OperationalQ1ConstructionRun state →
  Nat
runConstructionCost run =
  q1WitnessStateCount (q1Witness run)
  + length (auxiliaryTrace run)

stateCountBelowRunCost :
  ∀ {state : Q2.BoundedSelfReferenceState}
    (run : OperationalQ1ConstructionRun state) →
  q1WitnessStateCount (q1Witness run)
  ≤
  runConstructionCost run
stateCountBelowRunCost run =
  NatP.m≤m+n
    (q1WitnessStateCount (q1Witness run))
    (length (auxiliaryTrace run))

------------------------------------------------------------------------
-- Operational receipt -> previous charged witness.
--
-- The old free constructionCost is instantiated only by this derived cost.
------------------------------------------------------------------------

operationalRunToChargedWitness :
  ∀ {state : Q2.BoundedSelfReferenceState} →
  OperationalQ1ConstructionRun state →
  Charged.ConstructionChargedQ1StateWitness state
operationalRunToChargedWitness run =
  Charged.construction-charged-q1-state-witness
    (q1Witness run)
    (runConstructionCost run)
    (operationalAndNextStrict run)


------------------------------------------------------------------------
-- The actual constructor type now returns the operational run receipt.
------------------------------------------------------------------------

OperationalQ1StateConstructor : Set₁
OperationalQ1StateConstructor =
  (state : Q2.BoundedSelfReferenceState) →
  Maybe (OperationalQ1ConstructionRun state)

operationalConstructorToCharged :
  OperationalQ1StateConstructor →
  Charged.ConstructionChargedQ1StateConstructor
operationalConstructorToCharged constructor state
    with constructor state
... | nothing =
  nothing
... | just run =
  just (operationalRunToChargedWitness run)

operationalConstructorToQ2StepSystem :
  OperationalQ1StateConstructor →
  Q2.BoundedSelfReferenceStepSystem
operationalConstructorToQ2StepSystem constructor =
  Charged.chargedQ1ConstructorToQ2StepSystem
    (operationalConstructorToCharged constructor)

------------------------------------------------------------------------
-- Quantitative output-compression threshold.
------------------------------------------------------------------------

stateCountPlusNextStrict :
  ∀ {state : Q2.BoundedSelfReferenceState}
    (run : OperationalQ1ConstructionRun state) →
  q1WitnessStateCount (q1Witness run)
    +
    Q2.recursiveMeasure
      (Charged.q1WitnessNextState
        state
        (q1Witness run))
  <
  Q2.recursiveMeasure state
stateCountPlusNextStrict {state} run =
  NatP.≤-<-trans
    leftBelowOperational
    (operationalAndNextStrict run)
  where
    leftBelowOperational :
      q1WitnessStateCount (q1Witness run)
        +
        Q2.recursiveMeasure
          (Charged.q1WitnessNextState
            state
            (q1Witness run))
      ≤
      runConstructionCost run
        +
        Q2.recursiveMeasure
          (Charged.q1WitnessNextState
            state
            (q1Witness run))
    leftBelowOperational =
      NatP.+-mono-≤
        (stateCountBelowRunCost run)
        NatP.≤-refl

stateCountStrictlyBelowCurrentMeasure :
  ∀ {state : Q2.BoundedSelfReferenceState}
    (run : OperationalQ1ConstructionRun state) →
  q1WitnessStateCount (q1Witness run)
  <
  Q2.recursiveMeasure state
stateCountStrictlyBelowCurrentMeasure {state} run =
  NatP.≤-<-trans
    (NatP.m≤m+n
      (q1WitnessStateCount (q1Witness run))
      (Q2.recursiveMeasure
        (Charged.q1WitnessNextState
          state
          (q1Witness run))))
    (stateCountPlusNextStrict run)

------------------------------------------------------------------------
-- CLAY CONSEQUENCE
--
-- A Q1 mechanism can no longer attach a convenient small Nat to an expensive
-- constructor on this route.
--
-- Any successful live step must emit its quotient table and hence satisfy:
--
--   stateCount(Q) + measure(next(Q)) < measure(current).
--
-- Since next(Q) literally contains the compiled authority and the
-- quotation/rebinding payload, aggressive state compression and cheap class
-- selection are simultaneously necessary.
------------------------------------------------------------------------
