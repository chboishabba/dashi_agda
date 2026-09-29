module DASHI.Mathematics.Complexity.PNotEqualsNPCircuitSemanticSizeExact where

------------------------------------------------------------------------
-- IMPLEMENTATION-INVARIANT CIRCUIT SIZE
--
-- Raw gateCount is representation-sensitive: dead-gate padding can increase it
-- without changing the Boolean function.
--
-- The Clay-critical circuit lane therefore needs a semantic lower-bound notion:
--
--   bound <= size(C)
--
-- for EVERY concrete circuit C computing the same fixed-width Boolean
-- function.
--
-- This owner defines that invariant and proves that padding cannot manufacture
-- a semantic lower bound above the size of the original implementation.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥)
open import Data.Nat.Base using (_≤_; _<_)
open import Data.Vec.Base using (Vec)
import Data.Nat.Properties as NatP

import DASHI.Mathematics.Complexity.PNotEqualsNPConcreteBooleanCircuitDAGExact as Circuit
import DASHI.Mathematics.Complexity.PNotEqualsNPCircuitPaddingNoGoExact as Padding

------------------------------------------------------------------------
-- Pointwise circuit equivalence.
------------------------------------------------------------------------

SameCircuitFunction :
  ∀ {inputs : Nat} →
  Circuit.ConcreteBooleanCircuit inputs →
  Circuit.ConcreteBooleanCircuit inputs →
  Set
SameCircuitFunction {inputs} left right =
  (inputValues : Vec Bool inputs) →
  Circuit.evaluateCircuit left inputValues
  ≡ Circuit.evaluateCircuit right inputValues

sameCircuitFunctionRefl :
  ∀ {inputs : Nat}
    (circuit : Circuit.ConcreteBooleanCircuit inputs) →
  SameCircuitFunction circuit circuit
sameCircuitFunctionRefl circuit inputValues =
  refl

sameCircuitFunctionSym :
  ∀ {inputs : Nat}
    {left right : Circuit.ConcreteBooleanCircuit inputs} →
  SameCircuitFunction left right →
  SameCircuitFunction right left
sameCircuitFunctionSym same inputValues =
  NatEqSym (same inputValues)
  where
    NatEqSym :
      ∀ {A : Set} {x y : A} →
      x ≡ y →
      y ≡ x
    NatEqSym refl =
      refl

paddingPreservesCircuitFunction :
  ∀ {inputs : Nat}
    (extra : Nat)
    (circuit : Circuit.ConcreteBooleanCircuit inputs) →
  SameCircuitFunction
    (Padding.padCircuit extra circuit)
    circuit
paddingPreservesCircuitFunction extra circuit =
  Padding.padCircuitPreservesEvaluation extra circuit

------------------------------------------------------------------------
-- Lower bound relative to one represented function.
------------------------------------------------------------------------

CircuitFunctionSizeAtLeast :
  ∀ {inputs : Nat} →
  Circuit.ConcreteBooleanCircuit inputs →
  Nat →
  Set₁
CircuitFunctionSizeAtLeast {inputs} representative bound =
  (candidate : Circuit.ConcreteBooleanCircuit inputs) →
  SameCircuitFunction candidate representative →
  bound ≤ Circuit.circuitSize candidate

------------------------------------------------------------------------
-- Equivalent direct function-level form.
------------------------------------------------------------------------

FunctionCircuitSizeAtLeast :
  ∀ {inputs : Nat} →
  (Vec Bool inputs → Bool) →
  Nat →
  Set₁
FunctionCircuitSizeAtLeast {inputs} function bound =
  (candidate : Circuit.ConcreteBooleanCircuit inputs) →
  ((inputValues : Vec Bool inputs) →
    Circuit.evaluateCircuit candidate inputValues
    ≡ function inputValues) →
  bound ≤ Circuit.circuitSize candidate

representativeLowerBoundGivesFunctionLowerBound :
  ∀ {inputs : Nat}
    (representative : Circuit.ConcreteBooleanCircuit inputs)
    (bound : Nat) →
  CircuitFunctionSizeAtLeast representative bound →
  FunctionCircuitSizeAtLeast
    (Circuit.evaluateCircuit representative)
    bound
representativeLowerBoundGivesFunctionLowerBound
    representative bound lower candidate computes =
  lower candidate computes

functionLowerBoundGivesRepresentativeLowerBound :
  ∀ {inputs : Nat}
    (representative : Circuit.ConcreteBooleanCircuit inputs)
    (bound : Nat) →
  FunctionCircuitSizeAtLeast
    (Circuit.evaluateCircuit representative)
    bound →
  CircuitFunctionSizeAtLeast representative bound
functionLowerBoundGivesRepresentativeLowerBound
    representative bound lower candidate same =
  lower candidate same

------------------------------------------------------------------------
-- Padding cannot create semantic hardness.
------------------------------------------------------------------------

paddingCannotManufactureSemanticLowerBound :
  ∀ {inputs : Nat}
    (extra : Nat)
    (original : Circuit.ConcreteBooleanCircuit inputs)
    (claimedBound : Nat) →
  Circuit.circuitSize original < claimedBound →
  CircuitFunctionSizeAtLeast
    (Padding.padCircuit extra original)
    claimedBound →
  ⊥
paddingCannotManufactureSemanticLowerBound
    extra original claimedBound originalBelowClaim lower =
  NatP.<-irrefl
    (Circuit.circuitSize original)
    (NatP.<-≤-trans
      originalBelowClaim
      (lower
        original
        (sameCircuitFunctionSym
          (paddingPreservesCircuitFunction extra original))))

------------------------------------------------------------------------
-- Invariant frontier.
--
-- A statement such as
--
--   gateCount(compiledCandidateAtWidth n) > n
--
-- is not semantic hardness.  The circuit-normalized self-diagonal route must
-- instead establish a theorem of the form
--
--   FunctionCircuitSizeAtLeast SAT_n b(n)
--
-- (after a concrete fixed-width encoding of SAT instances is installed), or
-- explicitly justify a canonical compiler whose representation size is itself
-- part of the proof mechanism.
------------------------------------------------------------------------
