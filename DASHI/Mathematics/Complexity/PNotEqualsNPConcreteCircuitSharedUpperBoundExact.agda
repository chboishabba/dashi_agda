module DASHI.Mathematics.Complexity.PNotEqualsNPConcreteCircuitSharedUpperBoundExact where

------------------------------------------------------------------------
-- GENERIC LINEAR UPPER BOUND FOR THE SHARED/TSEITIN COMPILER
--
-- Existing shared compiler results give:
--
--   * one fresh variable per circuit gate;
--   * one local equivalence constraint per gate;
--   * exact existential semantics.
--
-- The lower-bound owner already proves gateCount <= formulaNodeCount.
--
-- This owner supplies the complementary UPPER bound needed by the
-- resource-closing self-diagonal route.
--
-- Every literal gate constraint has at most 13 syntax nodes:
--
--   constant gate :  9
--   NOT gate      : 11
--   AND/OR gate   : 13.
--
-- Therefore a g-gate program has shared-constraint syntax bounded by the
-- additive recurrence
--
--   U(0)   = 1
--   U(g+1) = 1 + U(g) + 13,
--
-- and the final acceptance formula adds only one conjunction plus one output
-- variable.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Data.Nat.Base using (_≤_)
import Data.Nat.Properties as NatP

import DASHI.Mathematics.Complexity.CookLevinCircuitGCTBoundary as Cook
import DASHI.Mathematics.Complexity.PNotEqualsNPConcreteBooleanCircuitDAGExact as Circuit
import DASHI.Mathematics.Complexity.PNotEqualsNPConcreteCircuitSharedCompilerExact as Compiler
import DASHI.Mathematics.Complexity.PNotEqualsNPConcreteCircuitSharedSemanticsExact as Semantics
import DASHI.Mathematics.Complexity.PNotEqualsNPProgramDescriptionFormulaEmbeddingExact as Size

------------------------------------------------------------------------
-- Literal gate-constraint upper bound.
------------------------------------------------------------------------

gateConstraintNodeCountAtMostThirteen :
  ∀ {inputs gates : Nat}
    (gate : Circuit.Gate inputs gates) →
  Size.formulaNodeCount
    (Compiler.gateConstraintFormula gate)
  ≤ 13
gateConstraintNodeCountAtMostThirteen
    (Circuit.constantGate value) =
  NatP.m≤m+n 9 4
gateConstraintNodeCountAtMostThirteen
    (Circuit.notGate source) =
  NatP.m≤m+n 11 2
gateConstraintNodeCountAtMostThirteen
    (Circuit.andGate left right) =
  NatP.≤-refl
gateConstraintNodeCountAtMostThirteen
    (Circuit.orGate left right) =
  NatP.≤-refl

------------------------------------------------------------------------
-- Linear recurrence for all shared constraints.
------------------------------------------------------------------------

sharedConstraintUpperBound :
  Nat →
  Nat
sharedConstraintUpperBound zero =
  suc zero
sharedConstraintUpperBound (suc gates) =
  suc
    (sharedConstraintUpperBound gates
     + 13)

programSharedConstraintNodeCountUpper :
  ∀ {inputs gates : Nat}
    (program : Circuit.GateProgram inputs gates) →
  Size.formulaNodeCount
    (Compiler.programSharedConstraints program)
  ≤
  sharedConstraintUpperBound gates
programSharedConstraintNodeCountUpper
    Circuit.noGates =
  NatP.≤-refl
programSharedConstraintNodeCountUpper
    (Circuit.appendGate previous gate) =
  s≤s
    (NatP.+-mono-≤
      (programSharedConstraintNodeCountUpper
        previous)
      (gateConstraintNodeCountAtMostThirteen
        gate))

------------------------------------------------------------------------
-- Output wire formula is always one variable node.
------------------------------------------------------------------------

circuitOutputFormulaHasOneNode :
  ∀ {inputs : Nat}
    (circuit :
      Circuit.ConcreteBooleanCircuit inputs) →
  Size.formulaNodeCount
    (Semantics.circuitOutputFormula circuit)
  ≡
  suc zero
circuitOutputFormulaHasOneNode circuit
    with Circuit.outputWire circuit
... | Circuit.inputWire index =
  refl
... | Circuit.gateWire index =
  refl

------------------------------------------------------------------------
-- Final authority upper bound.
------------------------------------------------------------------------

sharedAcceptanceUpperBound :
  Nat →
  Nat
sharedAcceptanceUpperBound gates =
  suc
    (sharedConstraintUpperBound gates
     + suc zero)

sharedAcceptanceFormulaNodeCountUpper :
  ∀ {inputs : Nat}
    (circuit :
      Circuit.ConcreteBooleanCircuit inputs) →
  Size.formulaNodeCount
    (Semantics.sharedAcceptanceFormula circuit)
  ≤
  sharedAcceptanceUpperBound
    (Circuit.circuitSize circuit)
sharedAcceptanceFormulaNodeCountUpper
    circuit =
  s≤s
    (NatP.+-mono-≤
      (programSharedConstraintNodeCountUpper
        (Circuit.program circuit))
      outputOne)
  where
    outputOne :
      Size.formulaNodeCount
        (Semantics.circuitOutputFormula circuit)
      ≤
      suc zero
    outputOne
      rewrite
        circuitOutputFormulaHasOneNode
          circuit =
      NatP.≤-refl

------------------------------------------------------------------------
-- Research consequence.
--
-- The ordinary shared SAT authority is linearly bounded in literal gate count.
-- Once a quotient circuit gate-count theorem is available, this upper bound
-- turns it directly into a formula-size budget rather than leaving resource
-- closure as an unconnected assumption.
------------------------------------------------------------------------
