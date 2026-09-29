module DASHI.Mathematics.Complexity.PNotEqualsNPCircuitPaddingNoGoExact where

------------------------------------------------------------------------
-- CIRCUIT-SIZE IMPLEMENTATION-DECORATION NO-GO
--
-- Clock tagging already showed that exact machine-state recurrence is not an
-- implementation-invariant lower-bound property.
--
-- The circuit-normalized lane has the analogous issue: raw gate count of an
-- arbitrary implementation is not semantic.  We can append dead gates which
-- are never referenced by the output, preserving the computed Boolean
-- function exactly while increasing structural gateCount.
--
-- Therefore a Clay-critical self-diagonal argument cannot treat
--
--   "the selected implementation C_n has more than n gates"
--
-- as an intrinsic hardness statement.  It must either:
--
--   * fix and justify a canonical compiler whose representation cost is part
--     of the theorem; or
--   * work with semantic/minimal circuit complexity (or another
--     implementation-invariant measure).
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Fin.Base using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Vec.Base using (Vec)

import DASHI.Mathematics.Complexity.PNotEqualsNPConcreteBooleanCircuitDAGExact as Circuit

------------------------------------------------------------------------
-- Existing gate references shift by one when a new newest gate is appended.
------------------------------------------------------------------------

liftWireAfterDeadAppend :
  ∀ {inputs gates : Nat} →
  Circuit.WireRef inputs gates →
  Circuit.WireRef inputs (suc gates)
liftWireAfterDeadAppend (Circuit.inputWire index) =
  Circuit.inputWire index
liftWireAfterDeadAppend (Circuit.gateWire index) =
  Circuit.gateWire (fsuc index)

------------------------------------------------------------------------
-- Append one unreachable constant gate.
------------------------------------------------------------------------

padCircuitOnce :
  ∀ {inputs : Nat} →
  Circuit.ConcreteBooleanCircuit inputs →
  Circuit.ConcreteBooleanCircuit inputs
padCircuitOnce
    (Circuit.concrete-boolean-circuit gates program output) =
  Circuit.concrete-boolean-circuit
    (suc gates)
    (Circuit.appendGate
      program
      (Circuit.constantGate false))
    (liftWireAfterDeadAppend output)

padCircuitOnceAddsOneGate :
  ∀ {inputs : Nat}
    (circuit : Circuit.ConcreteBooleanCircuit inputs) →
  Circuit.circuitSize (padCircuitOnce circuit)
  ≡ suc (Circuit.circuitSize circuit)
padCircuitOnceAddsOneGate
    (Circuit.concrete-boolean-circuit gates program output) =
  refl

padCircuitOncePreservesEvaluation :
  ∀ {inputs : Nat}
    (circuit : Circuit.ConcreteBooleanCircuit inputs)
    (inputValues : Vec Bool inputs) →
  Circuit.evaluateCircuit
      (padCircuitOnce circuit)
      inputValues
  ≡
  Circuit.evaluateCircuit
      circuit
      inputValues
padCircuitOncePreservesEvaluation
    (Circuit.concrete-boolean-circuit
      gates program (Circuit.inputWire index))
    inputValues =
  refl
padCircuitOncePreservesEvaluation
    (Circuit.concrete-boolean-circuit
      gates program (Circuit.gateWire index))
    inputValues =
  refl

------------------------------------------------------------------------
-- Arbitrarily many dead gates.
------------------------------------------------------------------------

padCircuit :
  ∀ {inputs : Nat} →
  Nat →
  Circuit.ConcreteBooleanCircuit inputs →
  Circuit.ConcreteBooleanCircuit inputs
padCircuit zero circuit =
  circuit
padCircuit (suc extra) circuit =
  padCircuit extra (padCircuitOnce circuit)

padCircuitPreservesEvaluation :
  ∀ {inputs : Nat}
    (extra : Nat)
    (circuit : Circuit.ConcreteBooleanCircuit inputs)
    (inputValues : Vec Bool inputs) →
  Circuit.evaluateCircuit
      (padCircuit extra circuit)
      inputValues
  ≡
  Circuit.evaluateCircuit
      circuit
      inputValues
padCircuitPreservesEvaluation zero circuit inputValues =
  refl
padCircuitPreservesEvaluation (suc extra) circuit inputValues =
  transitive
    (padCircuitPreservesEvaluation
      extra
      (padCircuitOnce circuit)
      inputValues)
    (padCircuitOncePreservesEvaluation
      circuit
      inputValues)
  where
    transitive :
      ∀ {A : Set} {left middle right : A} →
      left ≡ middle →
      middle ≡ right →
      left ≡ right
    transitive refl refl =
      refl

------------------------------------------------------------------------
-- Structural size grows at every padding step while semantics stays fixed.
------------------------------------------------------------------------

record SemanticPaddingStep
    {inputs : Nat}
    (original : Circuit.ConcreteBooleanCircuit inputs) : Set₁ where
  constructor semantic-padding-step
  field
    padded :
      Circuit.ConcreteBooleanCircuit inputs

    oneMoreGate :
      Circuit.circuitSize padded
      ≡ suc (Circuit.circuitSize original)

    sameFunction :
      (inputValues : Vec Bool inputs) →
      Circuit.evaluateCircuit padded inputValues
      ≡ Circuit.evaluateCircuit original inputValues

open SemanticPaddingStep public

oneDeadGateSemanticPadding :
  ∀ {inputs : Nat}
    (circuit : Circuit.ConcreteBooleanCircuit inputs) →
  SemanticPaddingStep circuit
oneDeadGateSemanticPadding circuit =
  semantic-padding-step
    (padCircuitOnce circuit)
    (padCircuitOnceAddsOneGate circuit)
    (padCircuitOncePreservesEvaluation circuit)

------------------------------------------------------------------------
-- Consequence.
--
-- Raw implementation size is decoration-sensitive.  The standard shared
-- compiler's lower bound
--
--   gateCount(C) <= formulaNodeCount(sharedConstraints(C))
--
-- is a correct statement about THAT representation, but padding shows that
-- gateCount(C) itself is not a language/function invariant.
------------------------------------------------------------------------
