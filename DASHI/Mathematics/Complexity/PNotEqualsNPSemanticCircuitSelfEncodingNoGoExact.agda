module DASHI.Mathematics.Complexity.PNotEqualsNPSemanticCircuitSelfEncodingNoGoExact where

------------------------------------------------------------------------
-- SEMANTIC CIRCUIT LOWER BOUND -> STANDARD SHARED SELF-ENCODING NO-GO
--
-- Raw implementation size is padding-sensitive.  The invariant replacement is
-- a function-level statement:
--
--   every concrete circuit computing f has at least b gates.
--
-- The standard shared-gate compiler separately proves:
--
--   gateCount(C) <= nodeCount(sharedConstraints(C)).
--
-- Combining them yields the implementation-independent obstruction:
--
--   if N < b,
--   no circuit computing f can have its standard shared constraint encoding
--   contain exactly N syntax nodes.
--
-- This is a route-specific theorem about the STANDARD shared encoding, not an
-- assertion that every conceivable proof/certificate for f must have size b.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥)
open import Data.Nat.Base using (_<_)
open import Data.Vec.Base using (Vec)
import Data.Nat.Properties as NatP

import DASHI.Mathematics.Complexity.PNotEqualsNPConcreteBooleanCircuitDAGExact as Circuit
import DASHI.Mathematics.Complexity.PNotEqualsNPCircuitSemanticSizeExact as Semantic
import DASHI.Mathematics.Complexity.PNotEqualsNPConcreteCircuitSharedCompilerExact as SharedCompiler
import DASHI.Mathematics.Complexity.PNotEqualsNPProgramDescriptionFormulaEmbeddingExact as FormulaSize

semanticCircuitLowerBoundBlocksStandardSharedSelfEncoding :
  ∀ {inputs : Nat}
    (function : Vec Bool inputs → Bool)
    (semanticLowerBound targetSize : Nat) →
  Semantic.FunctionCircuitSizeAtLeast
    function
    semanticLowerBound →
  targetSize < semanticLowerBound →
  (circuit : Circuit.ConcreteBooleanCircuit inputs) →
  ((inputValues : Vec Bool inputs) →
    Circuit.evaluateCircuit circuit inputValues
    ≡ function inputValues) →
  FormulaSize.formulaNodeCount
      (SharedCompiler.circuitSharedConstraints circuit)
    ≡ targetSize →
  ⊥
semanticCircuitLowerBoundBlocksStandardSharedSelfEncoding
    function semanticLowerBound targetSize
    lower targetBelowLower
    circuit computes sizeExact =
  NatP.<-irrefl
    targetSize
    (NatP.<-≤-trans
      targetBelowLower
      lowerBelowTarget)
  where
    lowerBelowCircuit :
      semanticLowerBound
      NatP.≤ Circuit.circuitSize circuit
    lowerBelowCircuit =
      lower circuit computes

    circuitBelowTarget :
      Circuit.circuitSize circuit
      NatP.≤ targetSize
    circuitBelowTarget =
      NatP.≤-trans
        (SharedCompiler.circuitGateCountBelowSharedConstraintNodeCount circuit)
        (NatP.≤-reflexive sizeExact)

    lowerBelowTarget :
      semanticLowerBound NatP.≤ targetSize
    lowerBelowTarget =
      NatP.≤-trans
        lowerBelowCircuit
        circuitBelowTarget

------------------------------------------------------------------------
-- Consequence for the self-diagonal route.
--
-- Once the candidate decision function at width n is represented as a fixed
-- Boolean function f_n, a standard one-variable/one-local-constraint-per-gate
-- self-encoding of target size N can close only if its semantic circuit
-- complexity is <= N.
--
-- Beating that obstruction requires either:
--
--   * a different proof/certificate system whose syntax is not lower-bounded
--     by ordinary circuit gate count; or
--   * special diagonal structure which yields a genuinely smaller equivalent
--     circuit for the self-input semantics.
------------------------------------------------------------------------
