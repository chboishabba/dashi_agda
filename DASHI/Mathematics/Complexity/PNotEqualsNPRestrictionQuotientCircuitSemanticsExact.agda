module DASHI.Mathematics.Complexity.PNotEqualsNPRestrictionQuotientCircuitSemanticsExact where

------------------------------------------------------------------------
-- QUOTIENT DP CIRCUIT SEMANTICS
--
-- Existing owners:
--
--   PNotEqualsNPRestrictionQuotientDynamicProgrammingExact
--   PNotEqualsNPRestrictionQuotientCircuitExact
--
-- construct respectively:
--
--   V_0(q)     = terminalTruth(q)
--   V_(d+1)(q) = V_d(step(q,false)) OR V_d(step(q,true))
--
-- and a literal zero-input acyclic Boolean circuit with one gate per
-- (depth,state).
--
-- This owner proves those are the SAME computation.
--
-- Main theorem:
--
--   evaluateCircuit(quotientCircuit quotient terminalTruth, [])
--     =
--   quotientTruthAtDepth
--     quotient labels rootVariables classify(root).
--
-- No quotient existence, terminal truth, or SAT lower bound is assumed here.
-- This closes the representation gap between the finite-state Shannon DP and
-- the concrete circuit/Tseitin pipeline.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Fin.Base as Fin using (Fin)
open import Data.Vec.Base using (Vec; []; _∷_)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)

import DASHI.Mathematics.Complexity.BooleanFormulaSATSelfReductionExact as SAT
import DASHI.Mathematics.Complexity.PNotEqualsNPSelfDiagonalRestrictionFamilyExact as Family
import DASHI.Mathematics.Complexity.PNotEqualsNPResourceClosingRestrictionQuotientExact as Quotient
import DASHI.Mathematics.Complexity.PNotEqualsNPRestrictionQuotientDynamicProgrammingExact as DP
import DASHI.Mathematics.Complexity.PNotEqualsNPRestrictionQuotientCircuitExact as QCircuit
import DASHI.Mathematics.Complexity.PNotEqualsNPConcreteBooleanCircuitDAGExact as Circuit
import DASHI.Mathematics.Complexity.PNotEqualsNPConcreteCircuitSharedSemanticsExact as Shared

------------------------------------------------------------------------
-- Local vector operations and exact lookup laws.
------------------------------------------------------------------------

appendVec :
  ∀ {A : Set} {left right : Nat} →
  Vec A left →
  Vec A right →
  Vec A (left + right)
appendVec [] rightValues =
  rightValues
appendVec (value ∷ values) rightValues =
  value ∷ appendVec values rightValues

mapVec :
  ∀ {A B : Set} {length : Nat} →
  (A → B) →
  Vec A length →
  Vec B length
mapVec function [] =
  []
mapVec function (value ∷ values) =
  function value ∷ mapVec function values

lookupMapVec :
  ∀ {A B : Set} {length : Nat}
    (function : A → B)
    (values : Vec A length)
    (index : Fin length) →
  Circuit.lookupVec
    index
    (mapVec function values)
  ≡
  function
    (Circuit.lookupVec index values)
lookupMapVec function (value ∷ values) Fin.zero =
  refl
lookupMapVec function (value ∷ values) (Fin.suc index) =
  lookupMapVec function values index

lookupNewestBlock :
  ∀ {A : Set}
    {newer older : Nat}
    (newValues : Vec A newer)
    (oldValues : Vec A older)
    (index : Fin newer) →
  Circuit.lookupVec
    (QCircuit.injectNewestBlock older index)
    (appendVec newValues oldValues)
  ≡
  Circuit.lookupVec index newValues
lookupNewestBlock
    (value ∷ values)
    oldValues
    Fin.zero =
  refl
lookupNewestBlock
    (value ∷ values)
    oldValues
    (Fin.suc index) =
  lookupNewestBlock
    values
    oldValues
    index

lookupOldBlock :
  ∀ {A : Set}
    {newer older : Nat}
    (newValues : Vec A newer)
    (oldValues : Vec A older)
    (index : Fin older) →
  Circuit.lookupVec
    (QCircuit.shiftPastNewer newer index)
    (appendVec newValues oldValues)
  ≡
  Circuit.lookupVec index oldValues
lookupOldBlock
    []
    oldValues
    index =
  refl
lookupOldBlock
    (value ∷ values)
    oldValues
    index =
  lookupOldBlock
    values
    oldValues
    index

------------------------------------------------------------------------
-- Terminal layer evaluates to the terminal state table.
------------------------------------------------------------------------

terminalLayerFromStatesEvaluation :
  ∀ {stateCount listed : Nat}
    (terminalTruth : Fin stateCount → Bool)
    (states : Vec (Fin stateCount) listed) →
  Circuit.evaluateProgram
    (QCircuit.terminalLayerFromStates
      terminalTruth
      states)
    []
  ≡
  mapVec terminalTruth states
terminalLayerFromStatesEvaluation
    terminalTruth
    [] =
  refl
terminalLayerFromStatesEvaluation
    terminalTruth
    (state ∷ states)
    rewrite
      terminalLayerFromStatesEvaluation
        terminalTruth
        states =
  refl

terminalLayerStateCorrect :
  (stateCount : Nat)
  (terminalTruth : Fin stateCount → Bool)
  (state : Fin stateCount) →
  Circuit.lookupVec
    state
    (Circuit.evaluateProgram
      (QCircuit.terminalLayer
        stateCount
        terminalTruth)
      [])
  ≡
  terminalTruth state
terminalLayerStateCorrect
    stateCount
    terminalTruth
    state =
  trans
    (cong
      (Circuit.lookupVec state)
      (terminalLayerFromStatesEvaluation
        terminalTruth
        (QCircuit.allStates stateCount)))
    (trans
      (lookupMapVec
        terminalTruth
        (QCircuit.allStates stateCount)
        state)
      (cong
        terminalTruth
        (Shared.lookupTabulateVec
          (λ inner → inner)
          state)))

------------------------------------------------------------------------
-- One recurrence layer evaluates to:
--
--   map state -> OR(old[step(state,0)], old[step(state,1)])
--   ++ old.
------------------------------------------------------------------------

recurrenceValue :
  ∀ {stateCount previousCount : Nat} →
  (step : Fin stateCount → Bool → Fin stateCount) →
  (previousStateWire : Fin stateCount → Fin previousCount) →
  Vec Bool previousCount →
  Fin stateCount →
  Bool
recurrenceValue step previousStateWire previousValues state =
  SAT.orBool
    (Circuit.lookupVec
      (previousStateWire (step state false))
      previousValues)
    (Circuit.lookupVec
      (previousStateWire (step state true))
      previousValues)

appendRecurrenceLayerEvaluation :
  ∀ {stateCount previousCount listed : Nat}
    (step : Fin stateCount → Bool → Fin stateCount)
    (previousStateWire : Fin stateCount → Fin previousCount)
    (states : Vec (Fin stateCount) listed)
    (previous : Circuit.GateProgram zero previousCount) →
  Circuit.evaluateProgram
    (QCircuit.appendRecurrenceLayerFromStates
      step
      previousStateWire
      states
      previous)
    []
  ≡
  appendVec
    (mapVec
      (recurrenceValue
        step
        previousStateWire
        (Circuit.evaluateProgram previous []))
      states)
    (Circuit.evaluateProgram previous [])
appendRecurrenceLayerEvaluation
    step
    previousStateWire
    []
    previous =
  refl
appendRecurrenceLayerEvaluation
    {listed = suc listed}
    step
    previousStateWire
    (state ∷ states)
    previous
    rewrite
      appendRecurrenceLayerEvaluation
        step
        previousStateWire
        states
        previous
      |
      lookupOldBlock
        (mapVec
          (recurrenceValue
            step
            previousStateWire
            (Circuit.evaluateProgram previous []))
          states)
        (Circuit.evaluateProgram previous [])
        (previousStateWire
          (step state false))
      |
      lookupOldBlock
        (mapVec
          (recurrenceValue
            step
            previousStateWire
            (Circuit.evaluateProgram previous []))
          states)
        (Circuit.evaluateProgram previous [])
        (previousStateWire
          (step state true)) =
  refl

------------------------------------------------------------------------
-- State lookup in one generated recurrence layer.
------------------------------------------------------------------------

recurrenceLayerStateCorrect :
  ∀ {stateCount previousCount : Nat}
    (step : Fin stateCount → Bool → Fin stateCount)
    (previousStateWire : Fin stateCount → Fin previousCount)
    (previous : Circuit.GateProgram zero previousCount)
    (state : Fin stateCount) →
  Circuit.lookupVec
    (QCircuit.injectNewestBlock
      previousCount
      state)
    (Circuit.evaluateProgram
      (QCircuit.appendRecurrenceLayerFromStates
        step
        previousStateWire
        (QCircuit.allStates stateCount)
        previous)
      [])
  ≡
  recurrenceValue
    step
    previousStateWire
    (Circuit.evaluateProgram previous [])
    state
recurrenceLayerStateCorrect
    {stateCount}
    {previousCount}
    step
    previousStateWire
    previous
    state =
  trans
    (cong
      (Circuit.lookupVec
        (QCircuit.injectNewestBlock
          previousCount
          state))
      (appendRecurrenceLayerEvaluation
        step
        previousStateWire
        (QCircuit.allStates stateCount)
        previous))
    (trans
      (lookupNewestBlock
        (mapVec
          (recurrenceValue
            step
            previousStateWire
            (Circuit.evaluateProgram previous []))
          (QCircuit.allStates stateCount))
        (Circuit.evaluateProgram previous [])
        state)
      (trans
        (lookupMapVec
          (recurrenceValue
            step
            previousStateWire
            (Circuit.evaluateProgram previous []))
          (QCircuit.allStates stateCount)
          state)
        (cong
          (recurrenceValue
            step
            previousStateWire
            (Circuit.evaluateProgram previous []))
          (Shared.lookupTabulateVec
            (λ inner → inner)
            state))))

------------------------------------------------------------------------
-- Main depth/state theorem.
------------------------------------------------------------------------

quotientProgramStateCorrect :
  ∀ {rootVariables : Nat}
    {root : SAT.BooleanFormula rootVariables}
    (quotient : Quotient.RestrictionSemanticQuotient root)
    (terminalTruth :
      Fin (Quotient.stateCount quotient) → Bool)
    (depth : Nat)
    (state : Fin (Quotient.stateCount quotient)) →
  Circuit.lookupVec
    (QCircuit.newestLayerWire depth state)
    (Circuit.evaluateProgram
      (QCircuit.quotientProgram
        quotient
        terminalTruth
        depth)
      [])
  ≡
  DP.quotientTruthAtDepth
    quotient
    (DP.terminal-state-labelling
      terminalTruth
      (λ derivation → refl))
    depth
    state
quotientProgramStateCorrect
    quotient
    terminalTruth
    zero
    state =
  terminalLayerStateCorrect
    (Quotient.stateCount quotient)
    terminalTruth
    state
quotientProgramStateCorrect
    quotient
    terminalTruth
    (suc depth)
    state =
  trans
    (recurrenceLayerStateCorrect
      (Quotient.step quotient)
      (QCircuit.newestLayerWire depth)
      (QCircuit.quotientProgram
        quotient
        terminalTruth
        depth)
      state)
    (cong₂
      SAT.orBool
      (quotientProgramStateCorrect
        quotient
        terminalTruth
        depth
        (Quotient.step quotient state false))
      (quotientProgramStateCorrect
        quotient
        terminalTruth
        depth
        (Quotient.step quotient state true)))

------------------------------------------------------------------------
-- The theorem above should not manufacture terminal correctness.  Package the
-- circuit/DP equality against an EXISTING terminal labelling.
------------------------------------------------------------------------

quotientProgramStateCorrectWithLabels :
  ∀ {rootVariables : Nat}
    {root : SAT.BooleanFormula rootVariables}
    (quotient : Quotient.RestrictionSemanticQuotient root)
    {oracle : SAT.SATDecisionOracle}
    (labels : DP.TerminalStateLabelling quotient oracle)
    (depth : Nat)
    (state : Fin (Quotient.stateCount quotient)) →
  Circuit.lookupVec
    (QCircuit.newestLayerWire depth state)
    (Circuit.evaluateProgram
      (QCircuit.quotientProgram
        quotient
        (DP.terminalTruth labels)
        depth)
      [])
  ≡
  DP.quotientTruthAtDepth
    quotient
    labels
    depth
    state
quotientProgramStateCorrectWithLabels
    quotient
    labels
    zero
    state =
  terminalLayerStateCorrect
    (Quotient.stateCount quotient)
    (DP.terminalTruth labels)
    state
quotientProgramStateCorrectWithLabels
    quotient
    labels
    (suc depth)
    state =
  trans
    (recurrenceLayerStateCorrect
      (Quotient.step quotient)
      (QCircuit.newestLayerWire depth)
      (QCircuit.quotientProgram
        quotient
        (DP.terminalTruth labels)
        depth)
      state)
    (cong₂
      SAT.orBool
      (quotientProgramStateCorrectWithLabels
        quotient
        labels
        depth
        (Quotient.step quotient state false))
      (quotientProgramStateCorrectWithLabels
        quotient
        labels
        depth
        (Quotient.step quotient state true)))

------------------------------------------------------------------------
-- Root circuit equals the exact quotient DP root value.
------------------------------------------------------------------------

quotientCircuitComputesDP :
  ∀ {rootVariables : Nat}
    {root : SAT.BooleanFormula rootVariables}
    (quotient : Quotient.RestrictionSemanticQuotient root)
    {oracle : SAT.SATDecisionOracle}
    (labels : DP.TerminalStateLabelling quotient oracle) →
  Circuit.evaluateCircuit
    (QCircuit.quotientCircuit
      quotient
      (DP.terminalTruth labels))
    []
  ≡
  DP.quotientTruthAtDepth
    quotient
    labels
    rootVariables
    (Quotient.classify
      quotient
      Family.restrictionRoot)
quotientCircuitComputesDP
    {rootVariables}
    quotient
    labels =
  quotientProgramStateCorrectWithLabels
    quotient
    labels
    rootVariables
    (Quotient.classify
      quotient
      Family.restrictionRoot)

------------------------------------------------------------------------
-- Compose with DP correctness: the concrete circuit computes exact SAT truth
-- of the root under any exact oracle supplying the terminal labels.
------------------------------------------------------------------------

quotientCircuitComputesRootDecision :
  ∀ {rootVariables : Nat}
    {root : SAT.BooleanFormula rootVariables}
    (quotient : Quotient.RestrictionSemanticQuotient root)
    (oracle : SAT.SATDecisionOracle)
    (labels : DP.TerminalStateLabelling quotient oracle) →
  Circuit.evaluateCircuit
    (QCircuit.quotientCircuit
      quotient
      (DP.terminalTruth labels))
    []
  ≡
  Search.decide oracle root
quotientCircuitComputesRootDecision
    quotient
    oracle
    labels =
  trans
    (quotientCircuitComputesDP
      quotient
      labels)
    (DP.quotientTruthComputesRootDecision
      quotient
      oracle
      labels)

------------------------------------------------------------------------
-- Research consequence.
--
-- The finite quotient route now has an exact executable closure:
--
--   root restriction family
--      -> quotient states
--      -> depth/state DP
--      -> literal zero-input circuit
--      -> exact root SAT bit.
--
-- Together with PNotEqualsNPConcreteCircuitSharedSemanticsExact, that circuit
-- can be compiled to an ordinary SAT formula without another semantic gap.
--
-- What remains genuinely OPEN is construction of the quotient / strict
-- representatives / terminal authority from the special self-instantiation
-- structure while closing the self-size budget.
------------------------------------------------------------------------
