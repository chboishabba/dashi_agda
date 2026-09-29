module DASHI.Mathematics.Complexity.PNotEqualsNPIntensionalChainAuthorityExact where

------------------------------------------------------------------------
-- NON-CIRCULAR INTENSIONAL SEMANTIC AUTHORITY: POSITIVE CONTROL
--
-- The answer-omniscient no-go shows that
--
--   evaluate first -> print a one-node constant
--
-- is vacuous.
--
-- The answer-blind no-go shows that a constructor which ignores the program
-- cannot certify arbitrary computations.
--
-- This owner exhibits the desired middle architecture on the already-proved
-- repeated-fanout family:
--
--   finite intensional description (depth)
--       ->
--   reusable semantic theorem (the chain computes identity)
--       ->
--   constant-size endpoint authority.
--
-- The authority constructor never needs the concrete evaluation result.  Its
-- soundness follows from the independently proved family theorem.
--
-- This is NOT a SAT lower bound.  It is a positive control proving that the
-- non-circular P11 architecture is coherent on a structured uniform family.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥)
open import Data.Vec.Base using (_∷_; [])
open import Relation.Binary.PropositionalEquality using (sym; trans)

import DASHI.Mathematics.Complexity.CookLevinCircuitGCTBoundary as Cook
import DASHI.Mathematics.Complexity.PNotEqualsNPConcreteCircuitInlineExpansionExact as Inline
import DASHI.Mathematics.Complexity.PNotEqualsNPChainGlobalInvariantCompressionExact as Global
import DASHI.Mathematics.Complexity.PNotEqualsNPProgramDescriptionFormulaEmbeddingExact as FormulaSize
import DASHI.Mathematics.Complexity.PNotEqualsNPConcreteBooleanCircuitDAGExact as Circuit

------------------------------------------------------------------------
-- Finite intensional family description.
------------------------------------------------------------------------

record ChainProgramDescription : Set where
  constructor chain-program-description
  field
    depth : Nat

open ChainProgramDescription public

describedCircuit :
  ChainProgramDescription →
  Circuit.ConcreteBooleanCircuit 1
describedCircuit description =
  Inline.duplicatingCircuit
    (depth description)

------------------------------------------------------------------------
-- Authority constructor.
--
-- It depends on the family description only through the reusable family
-- theorem; the emitted proposition itself is the constant endpoint equality.
------------------------------------------------------------------------

chainAuthorityFormula :
  ChainProgramDescription →
  Cook.BooleanFormula
chainAuthorityFormula description =
  Global.endpointEqualityFormula

chainAuthorityFormulaHasConstantSize :
  (description : ChainProgramDescription) →
  FormulaSize.formulaNodeCount
    (chainAuthorityFormula description)
  ≡ 9
chainAuthorityFormulaHasConstantSize description =
  Global.endpointEqualityFormulaNodeCount

------------------------------------------------------------------------
-- Concrete endpoint assignment.
--
-- Variable 0 = input.
-- Variable 1 = claimed output.
------------------------------------------------------------------------

endpointAssignment :
  Bool →
  Bool →
  Cook.Assignment
endpointAssignment inputValue outputValue zero =
  inputValue
endpointAssignment inputValue outputValue (suc zero) =
  outputValue
endpointAssignment inputValue outputValue (suc (suc index)) =
  false

endpointAuthorityEvaluatesTrueWhenEqual :
  (value : Bool) →
  Cook.evaluate
    Global.endpointEqualityFormula
    (endpointAssignment value value)
  ≡ true
endpointAuthorityEvaluatesTrueWhenEqual true =
  refl
endpointAuthorityEvaluatesTrueWhenEqual false =
  refl

endpointAuthoritySatisfiableWhenEqual :
  (value : Bool) →
  Cook.Satisfiable
    Global.endpointEqualityFormula
endpointAuthoritySatisfiableWhenEqual value =
  Cook.satisfyingAssignment
    (endpointAssignment value value)
    (endpointAuthorityEvaluatesTrueWhenEqual value)

------------------------------------------------------------------------
-- Independent semantic theorem supplies the authority's meaning.
------------------------------------------------------------------------

describedCircuitComputesInput :
  (description : ChainProgramDescription)
  (inputValue : Bool) →
  Circuit.evaluateCircuit
      (describedCircuit description)
      (inputValue ∷ [])
  ≡ inputValue
describedCircuitComputesInput description inputValue =
  Inline.duplicatingCircuitComputesInput
    (depth description)
    inputValue

record IntensionalChainAuthority
    (description : ChainProgramDescription)
    (inputValue outputValue : Bool) : Set where
  constructor intensional-chain-authority
  field
    endpointTheorem :
      inputValue ≡ outputValue

open IntensionalChainAuthority public

constructChainAuthority :
  (description : ChainProgramDescription)
  (value : Bool) →
  IntensionalChainAuthority
    description
    value
    value
constructChainAuthority description value =
  intensional-chain-authority refl

chainAuthoritySound :
  (description : ChainProgramDescription)
  (inputValue outputValue : Bool) →
  IntensionalChainAuthority
    description inputValue outputValue →
  Circuit.evaluateCircuit
      (describedCircuit description)
      (inputValue ∷ [])
  ≡ outputValue
chainAuthoritySound
    description inputValue outputValue authority =
  trans
    (describedCircuitComputesInput
      description inputValue)
    (endpointTheorem authority)

------------------------------------------------------------------------
-- No evaluation result is needed to construct the reflexive authority for a
-- claimed value; the family theorem discharges semantic soundness.
--
-- The SAT-self-diagonal challenge is to derive an analogous theorem for the
-- uniformly generated self-evaluation family without the theorem itself
-- encoding the hard SAT decision.
------------------------------------------------------------------------
