module DASHI.Mathematics.Complexity.PNotEqualsNPRestrictionQuotientCircuitExact where

------------------------------------------------------------------------
-- FINITE RESTRICTION QUOTIENT -> LITERAL ACYCLIC BOOLEAN CIRCUIT
--
-- Given:
--
--   quotient : finite root-scoped restriction quotient
--   labels   : terminal truth value for each quotient state
--
-- construct a ZERO-INPUT concrete circuit with one gate per (depth,state):
--
--   depth 0:
--     v[0,q] := terminalTruth(q)
--
--   depth d+1:
--     v[d+1,q] :=
--       v[d,step(q,false)] OR v[d,step(q,true)].
--
-- The output is v[rootVariables, classify(root)].
--
-- Gate count is exactly:
--
--   (rootVariables + 1) * stateCount.
--
-- This turns the abstract depth/state DP into the literal concrete DAG accepted
-- by the now-semantically-exact shared/Tseitin compiler.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Data.Fin.Base as Fin using (Fin)
open import Data.Vec.Base using (Vec; []; _∷_)

import DASHI.Mathematics.Complexity.BooleanFormulaSATSelfReductionExact as SAT
import DASHI.Mathematics.Complexity.PNotEqualsNPSelfDiagonalRestrictionFamilyExact as Family
import DASHI.Mathematics.Complexity.PNotEqualsNPResourceClosingRestrictionQuotientExact as Quotient
import DASHI.Mathematics.Complexity.PNotEqualsNPRestrictionQuotientDynamicProgrammingExact as DP
import DASHI.Mathematics.Complexity.PNotEqualsNPConcreteBooleanCircuitDAGExact as Circuit
import DASHI.Mathematics.Complexity.PNotEqualsNPConcreteCircuitSharedSemanticsExact as SharedSemantics

------------------------------------------------------------------------
-- Canonical finite state vector.
------------------------------------------------------------------------

allStates :
  (stateCount : Nat) →
  Vec (Fin stateCount) stateCount
allStates stateCount =
  SharedSemantics.tabulateVec
    (λ state → state)

------------------------------------------------------------------------
-- Finite-index embeddings.
------------------------------------------------------------------------

injectNewestBlock :
  ∀ {blockSize : Nat} →
  (olderSize : Nat) →
  Fin blockSize →
  Fin (blockSize + olderSize)
injectNewestBlock olderSize Fin.zero =
  Fin.zero
injectNewestBlock olderSize (Fin.suc index) =
  Fin.suc
    (injectNewestBlock
      olderSize
      index)

shiftPastNewer :
  (newerSize : Nat) →
  ∀ {olderSize : Nat} →
  Fin olderSize →
  Fin (newerSize + olderSize)
shiftPastNewer zero index =
  index
shiftPastNewer (suc newerSize) index =
  Fin.suc
    (shiftPastNewer
      newerSize
      index)

------------------------------------------------------------------------
-- Terminal layer: one constant gate per quotient state.
--
-- Recursing on the tail first means the final newest-first gate vector follows
-- the same order as the input state vector.
------------------------------------------------------------------------

terminalLayerFromStates :
  ∀ {stateCount listed : Nat} →
  (terminalTruth : Fin stateCount → Bool) →
  Vec (Fin stateCount) listed →
  Circuit.GateProgram zero listed
terminalLayerFromStates terminalTruth [] =
  Circuit.noGates
terminalLayerFromStates terminalTruth (state ∷ states) =
  Circuit.appendGate
    (terminalLayerFromStates
      terminalTruth
      states)
    (Circuit.constantGate
      (terminalTruth state))

terminalLayer :
  (stateCount : Nat) →
  (terminalTruth : Fin stateCount → Bool) →
  Circuit.GateProgram zero stateCount
terminalLayer stateCount terminalTruth =
  terminalLayerFromStates
    terminalTruth
    (allStates stateCount)

------------------------------------------------------------------------
-- Append one Shannon recurrence layer.
------------------------------------------------------------------------

appendRecurrenceLayerFromStates :
  ∀ {stateCount previousCount listed : Nat} →
  (step : Fin stateCount → Bool → Fin stateCount) →
  (previousStateWire :
    Fin stateCount →
    Fin previousCount) →
  Vec (Fin stateCount) listed →
  Circuit.GateProgram zero previousCount →
  Circuit.GateProgram
    zero
    (listed + previousCount)
appendRecurrenceLayerFromStates
    step previousStateWire [] previous =
  previous
appendRecurrenceLayerFromStates
    {listed = suc listed}
    step previousStateWire
    (state ∷ states)
    previous =
  Circuit.appendGate
    recursivelyBuilt
    (Circuit.orGate
      (Circuit.gateWire
        (shiftPastNewer
          listed
          (previousStateWire
            (step state false))))
      (Circuit.gateWire
        (shiftPastNewer
          listed
          (previousStateWire
            (step state true)))))
  where
    recursivelyBuilt :
      Circuit.GateProgram
        zero
        (listed + previousCount)
    recursivelyBuilt =
      appendRecurrenceLayerFromStates
        step
        previousStateWire
        states
        previous

------------------------------------------------------------------------
-- Total gate count after depth d.
--
-- Depth zero already contains the terminal state layer.
------------------------------------------------------------------------

quotientGateCount :
  Nat →
  Nat →
  Nat
quotientGateCount stateCount zero =
  stateCount
quotientGateCount stateCount (suc depth) =
  stateCount
  +
  quotientGateCount stateCount depth

quotientGateCountExact :
  (stateCount depth : Nat) →
  quotientGateCount stateCount depth
  ≡
  suc depth * stateCount
quotientGateCountExact stateCount zero =
  refl
quotientGateCountExact stateCount (suc depth)
    rewrite
      quotientGateCountExact
        stateCount
        depth =
  refl

------------------------------------------------------------------------
-- Newest-layer wire embedding.
------------------------------------------------------------------------

newestLayerWire :
  ∀ {stateCount : Nat}
    (depth : Nat) →
  Fin stateCount →
  Fin (quotientGateCount stateCount depth)
newestLayerWire {stateCount} zero state =
  state
newestLayerWire {stateCount} (suc depth) state =
  injectNewestBlock
    (quotientGateCount
      stateCount
      depth)
    state

------------------------------------------------------------------------
-- Complete quotient DP gate program.
------------------------------------------------------------------------

quotientProgram :
  ∀ {rootVariables : Nat}
    {root : SAT.BooleanFormula rootVariables} →
  (quotient :
    Quotient.RestrictionSemanticQuotient root) →
  (terminalTruth :
    Fin (Quotient.stateCount quotient) →
    Bool) →
  (depth : Nat) →
  Circuit.GateProgram
    zero
    (quotientGateCount
      (Quotient.stateCount quotient)
      depth)
quotientProgram quotient terminalTruth zero =
  terminalLayer
    (Quotient.stateCount quotient)
    terminalTruth
quotientProgram
    quotient terminalTruth
    (suc depth) =
  appendRecurrenceLayerFromStates
    (Quotient.step quotient)
    (newestLayerWire depth)
    (allStates
      (Quotient.stateCount quotient))
    (quotientProgram
      quotient
      terminalTruth
      depth)

------------------------------------------------------------------------
-- Root-state output circuit.
------------------------------------------------------------------------

quotientCircuit :
  ∀ {rootVariables : Nat}
    {root : SAT.BooleanFormula rootVariables} →
  (quotient :
    Quotient.RestrictionSemanticQuotient root) →
  (terminalTruth :
    Fin (Quotient.stateCount quotient) →
    Bool) →
  Circuit.ConcreteBooleanCircuit zero
quotientCircuit
    {rootVariables}
    quotient
    terminalTruth =
  Circuit.concrete-boolean-circuit
    (quotientGateCount
      (Quotient.stateCount quotient)
      rootVariables)
    (quotientProgram
      quotient
      terminalTruth
      rootVariables)
    (Circuit.gateWire
      (newestLayerWire
        rootVariables
        rootState))
  where
    rootState :
      Fin (Quotient.stateCount quotient)
    rootState =
      Quotient.classify
        quotient
        Family.restrictionRoot

quotientCircuitGateCount :
  ∀ {rootVariables : Nat}
    {root : SAT.BooleanFormula rootVariables}
    (quotient :
      Quotient.RestrictionSemanticQuotient root)
    (terminalTruth :
      Fin (Quotient.stateCount quotient) →
      Bool) →
  Circuit.circuitSize
    (quotientCircuit
      quotient
      terminalTruth)
  ≡
  suc rootVariables
    * Quotient.stateCount quotient
quotientCircuitGateCount
    {rootVariables}
    quotient
    terminalTruth =
  quotientGateCountExact
    (Quotient.stateCount quotient)
    rootVariables

------------------------------------------------------------------------
-- Research boundary.
--
-- Syntax/gate-count construction is now literal.  The next theorem must prove:
--
--   evaluateCircuit(quotientCircuit, [])
--     =
--   DP.quotientTruthAtDepth(...root state...).
--
-- Once that is paid, generic shared compiler exactness immediately produces an
-- ordinary SAT authority formula of linear-in-(depth*states) gate structure.
------------------------------------------------------------------------
