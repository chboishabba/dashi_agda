module DASHI.Mathematics.Complexity.PNotEqualsNPConcreteCircuitSharedConstraintExact where

------------------------------------------------------------------------
-- AUXILIARY-VARIABLE SHARING FOR A CONCRETE CIRCUIT FAMILY
--
-- PNotEqualsNPConcreteCircuitInlineExpansionExact proves that recursively
-- inlining a shared repeated-fanout DAG obeys
--
--   S(d+1) = 1 + 2*S(d),
--
-- even though the circuit itself has only d gates.
--
-- Here we construct the complementary positive result for that SAME family:
-- allocate one fresh Boolean variable per gate and assert one local
-- equivalence constraint per gate.
--
-- The resulting syntax obeys the additive recurrence
--
--   A(0)   = 1
--   A(d+1) = 1 + A(d) + 13,
--
-- so DAG sharing is genuinely retained by auxiliary variables.
--
-- This is not P != NP: the shared encoding is still linear in the number of
-- circuit gates.  It removes accidental tree-duplication and isolates the real
-- diagonal size question:
--
--   can the self-generated formula of size N soundly encode/evaluate a
--   circuit C_N whose gate count is superlinear in N?
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)

import DASHI.Mathematics.Complexity.CookLevinCircuitGCTBoundary as Cook
import DASHI.Mathematics.Complexity.PNotEqualsNPProgramDescriptionFormulaEmbeddingExact as FormulaSize

------------------------------------------------------------------------
-- Boolean equivalence as ordinary formula syntax.
------------------------------------------------------------------------

equivalenceFormula :
  Cook.BooleanFormula →
  Cook.BooleanFormula →
  Cook.BooleanFormula
equivalenceFormula left right =
  Cook.disjunction
    (Cook.conjunction left right)
    (Cook.conjunction
      (Cook.negate left)
      (Cook.negate right))

equivalenceFormulaReflexive :
  (value : Bool) →
  Cook.evaluate
    (equivalenceFormula
      (Cook.constant value)
      (Cook.constant value))
    (λ index → false)
  ≡ true
equivalenceFormulaReflexive true =
  refl
equivalenceFormulaReflexive false =
  refl

------------------------------------------------------------------------
-- Repeated-fanout gate numbering.
--
-- Input x is variable 0.
-- Gate g writes fresh variable 1+g.
-- Gate 0 reads x.
-- Gate (g+1) reads the preceding gate variable 1+g.
------------------------------------------------------------------------

gateOutputIndex : Nat → Nat
gateOutputIndex gate =
  suc gate

gateSourceIndex : Nat → Nat
gateSourceIndex zero =
  zero
gateSourceIndex (suc gate) =
  suc gate

chainGateConstraint :
  Nat →
  Cook.BooleanFormula
chainGateConstraint gate =
  equivalenceFormula
    (Cook.variable (gateOutputIndex gate))
    (Cook.conjunction
      (Cook.variable (gateSourceIndex gate))
      (Cook.variable (gateSourceIndex gate)))

------------------------------------------------------------------------
-- Each gate constraint has constant syntax size 13.
------------------------------------------------------------------------

chainGateConstraintNodeCount :
  (gate : Nat) →
  FormulaSize.formulaNodeCount (chainGateConstraint gate)
  ≡ 13
chainGateConstraintNodeCount gate =
  refl

------------------------------------------------------------------------
-- Conjunction of all gate constraints.
------------------------------------------------------------------------

chainConstraints :
  Nat →
  Cook.BooleanFormula
chainConstraints zero =
  Cook.constant true
chainConstraints (suc depth) =
  Cook.conjunction
    (chainConstraints depth)
    (chainGateConstraint depth)

sharedChainSize : Nat → Nat
sharedChainSize zero =
  suc zero
sharedChainSize (suc depth) =
  suc (sharedChainSize depth + 13)

chainConstraintsNodeCount :
  (depth : Nat) →
  FormulaSize.formulaNodeCount (chainConstraints depth)
  ≡ sharedChainSize depth
chainConstraintsNodeCount zero =
  refl
chainConstraintsNodeCount (suc depth)
    rewrite chainConstraintsNodeCount depth
          | chainGateConstraintNodeCount depth =
  refl

sharedChainSizeStep :
  (depth : Nat) →
  sharedChainSize (suc depth)
  ≡ suc (sharedChainSize depth + 13)
sharedChainSizeStep depth =
  refl

------------------------------------------------------------------------
-- Semantic consistency of the shared representation.
--
-- On the repeated-fanout circuit, if input x has value b then every gate also
-- has value b.  The constant assignment b to all variables therefore satisfies
-- every local equivalence constraint.  This provides a literal SAT witness for
-- the shared gate relation rather than only a size calculation.
------------------------------------------------------------------------

chainGateConstraintTrueUnderConstantAssignment :
  (gate : Nat)
  (value : Bool) →
  Cook.evaluate
    (chainGateConstraint gate)
    (λ index → value)
  ≡ true
chainGateConstraintTrueUnderConstantAssignment gate true =
  refl
chainGateConstraintTrueUnderConstantAssignment gate false =
  refl

chainConstraintsTrueUnderConstantAssignment :
  (depth : Nat)
  (value : Bool) →
  Cook.evaluate
    (chainConstraints depth)
    (λ index → value)
  ≡ true
chainConstraintsTrueUnderConstantAssignment zero value =
  refl
chainConstraintsTrueUnderConstantAssignment
    (suc depth) value
    rewrite
      chainConstraintsTrueUnderConstantAssignment depth value
      |
      chainGateConstraintTrueUnderConstantAssignment depth value =
  refl

chainConstraintsSatisfiable :
  (depth : Nat) →
  Cook.Satisfiable (chainConstraints depth)
chainConstraintsSatisfiable depth =
  Cook.satisfyingAssignment
    (λ index → false)
    (chainConstraintsTrueUnderConstantAssignment depth false)

------------------------------------------------------------------------
-- Bind the circuit input and requested output as well.
------------------------------------------------------------------------

literalFor :
  Nat →
  Bool →
  Cook.BooleanFormula
literalFor index true =
  Cook.variable index
literalFor index false =
  Cook.negate (Cook.variable index)

chainOutputIndex : Nat → Nat
chainOutputIndex zero =
  zero
chainOutputIndex (suc depth) =
  suc depth

sharedChainEvaluationFormula :
  Nat →
  Bool →
  Cook.BooleanFormula
sharedChainEvaluationFormula depth value =
  Cook.conjunction
    (literalFor zero value)
    (Cook.conjunction
      (chainConstraints depth)
      (literalFor (chainOutputIndex depth) value))

sharedChainEvaluationFormulaSatisfied :
  (depth : Nat)
  (value : Bool) →
  Cook.evaluate
    (sharedChainEvaluationFormula depth value)
    (λ index → value)
  ≡ true
sharedChainEvaluationFormulaSatisfied depth true
    rewrite chainConstraintsTrueUnderConstantAssignment depth true =
  refl
sharedChainEvaluationFormulaSatisfied depth false
    rewrite chainConstraintsTrueUnderConstantAssignment depth false =
  refl

sharedChainEvaluationFormulaIsSatisfiable :
  (depth : Nat)
  (value : Bool) →
  Cook.Satisfiable
    (sharedChainEvaluationFormula depth value)
sharedChainEvaluationFormulaIsSatisfiable depth value =
  Cook.satisfyingAssignment
    (λ index → value)
    (sharedChainEvaluationFormulaSatisfied depth value)

------------------------------------------------------------------------
-- Exact evaluation-formula size recurrence.
--
-- The input/output literals add only constant syntax around the additive
-- constraint body.  We retain the exact body recurrence above as the key
-- sharing theorem; no exponential substitution occurs.
------------------------------------------------------------------------

sharedEncodingRetainsDAGSharing :
  (depth : Nat) →
  FormulaSize.formulaNodeCount (chainConstraints (suc depth))
  ≡ suc (sharedChainSize depth + 13)
sharedEncodingRetainsDAGSharing depth
    rewrite chainConstraintsNodeCount (suc depth) =
  refl
