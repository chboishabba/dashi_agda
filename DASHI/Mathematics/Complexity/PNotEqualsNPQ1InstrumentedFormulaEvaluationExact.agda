module DASHI.Mathematics.Complexity.PNotEqualsNPQ1InstrumentedFormulaEvaluationExact where

------------------------------------------------------------------------
-- EAGER FORMULA INTERPRETER WITH ACTUAL STRUCTURAL WORK COUNT
--
-- Unlike a "one row = one unit" estimate, each Boolean formula evaluation is
-- performed by the instrumented interpreter below. It computes the SAME Bool
-- as SAT.evaluate and charges each visited syntax node. Both children of a
-- binary operator are evaluated, so this is an exact eager execution model.
--
-- The total truth-table evaluation cost on a rooted layer can now account for
-- all syntactic subformulas visited at every assignment.
--
-- This is a concrete evaluator cost, NOT a full tape/RAM instruction cost:
-- assignment indexing, allocation, key comparison, representative search and
-- transition-table materialization remain separate.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (cong; cong₂)

import DASHI.Mathematics.Complexity.BooleanFormulaSATSelfReductionExact as SAT
import DASHI.Mathematics.Complexity.PNotEqualsNPSelfDiagonalRestrictionFamilyExact as Family
import DASHI.Mathematics.Complexity.PNotEqualsNPSelfDiagonalResidualWidthExact as Width
import DASHI.Mathematics.Complexity.PNotEqualsNPExactResidualSummaryBitLowerBoundExact as Bits
import DASHI.Mathematics.Complexity.PNotEqualsNPQ1RootedExhaustiveMergeExact as Root

------------------------------------------------------------------------
-- Each syntax constructor costs one visit; all binary children are visited.
------------------------------------------------------------------------

formulaNodeVisits :
  ∀ {variables : Nat} →
  SAT.BooleanFormula variables →
  Nat
formulaNodeVisits (SAT.variable index) = suc zero
formulaNodeVisits (SAT.constant value) = suc zero
formulaNodeVisits (SAT.negate formula) =
  suc (formulaNodeVisits formula)
formulaNodeVisits (SAT.conjunction left right) =
  suc (formulaNodeVisits left + formulaNodeVisits right)
formulaNodeVisits (SAT.disjunction left right) =
  suc (formulaNodeVisits left + formulaNodeVisits right)

evaluateWithNodeVisits :
  ∀ {variables : Nat} →
  SAT.BooleanFormula variables →
  SAT.Assignment variables →
  Bool × Nat
evaluateWithNodeVisits (SAT.variable index) assignment =
  assignment index , suc zero
evaluateWithNodeVisits (SAT.constant value) assignment =
  value , suc zero
evaluateWithNodeVisits (SAT.negate formula) assignment
    with evaluateWithNodeVisits formula assignment
... | value , work =
  SAT.notBool value , suc work
evaluateWithNodeVisits (SAT.conjunction left right) assignment
    with evaluateWithNodeVisits left assignment
       | evaluateWithNodeVisits right assignment
... | leftValue , leftWork | rightValue , rightWork =
  SAT.andBool leftValue rightValue ,
  suc (leftWork + rightWork)
evaluateWithNodeVisits (SAT.disjunction left right) assignment
    with evaluateWithNodeVisits left assignment
       | evaluateWithNodeVisits right assignment
... | leftValue , leftWork | rightValue , rightWork =
  SAT.orBool leftValue rightValue ,
  suc (leftWork + rightWork)

------------------------------------------------------------------------
-- Evaluator value agrees with the actual SAT owner by structural induction.
------------------------------------------------------------------------

instrumentedValueExact :
  ∀ {variables : Nat}
    (formula : SAT.BooleanFormula variables)
    (assignment : SAT.Assignment variables) →
  proj₁ (evaluateWithNodeVisits formula assignment)
  ≡ SAT.evaluate formula assignment
instrumentedValueExact (SAT.variable index) assignment =
  refl
instrumentedValueExact (SAT.constant value) assignment =
  refl
instrumentedValueExact (SAT.negate formula) assignment
    with evaluateWithNodeVisits formula assignment
       | instrumentedValueExact formula assignment
... | value , work | exact =
  cong SAT.notBool exact
instrumentedValueExact (SAT.conjunction left right) assignment
    with evaluateWithNodeVisits left assignment
       | evaluateWithNodeVisits right assignment
       | instrumentedValueExact left assignment
       | instrumentedValueExact right assignment
... | leftValue , leftWork
    | rightValue , rightWork
    | leftExact
    | rightExact =
  cong₂ SAT.andBool leftExact rightExact
instrumentedValueExact (SAT.disjunction left right) assignment
    with evaluateWithNodeVisits left assignment
       | evaluateWithNodeVisits right assignment
       | instrumentedValueExact left assignment
       | instrumentedValueExact right assignment
... | leftValue , leftWork
    | rightValue , rightWork
    | leftExact
    | rightExact =
  cong₂ SAT.orBool leftExact rightExact

------------------------------------------------------------------------
-- Eager-node charge is exact for EVERY input assignment.
------------------------------------------------------------------------

instrumentedWorkExact :
  ∀ {variables : Nat}
    (formula : SAT.BooleanFormula variables)
    (assignment : SAT.Assignment variables) →
  proj₂ (evaluateWithNodeVisits formula assignment)
  ≡ formulaNodeVisits formula
instrumentedWorkExact (SAT.variable index) assignment =
  refl
instrumentedWorkExact (SAT.constant value) assignment =
  refl
instrumentedWorkExact (SAT.negate formula) assignment
    with evaluateWithNodeVisits formula assignment
       | instrumentedWorkExact formula assignment
... | value , work | exact =
  cong suc exact
instrumentedWorkExact (SAT.conjunction left right) assignment
    with evaluateWithNodeVisits left assignment
       | evaluateWithNodeVisits right assignment
       | instrumentedWorkExact left assignment
       | instrumentedWorkExact right assignment
... | leftValue , leftWork
    | rightValue , rightWork
    | leftExact
    | rightExact =
  cong suc (cong₂ _+_ leftExact rightExact)
instrumentedWorkExact (SAT.disjunction left right) assignment
    with evaluateWithNodeVisits left assignment
       | evaluateWithNodeVisits right assignment
       | instrumentedWorkExact left assignment
       | instrumentedWorkExact right assignment
... | leftValue , leftWork
    | rightValue , rightWork
    | leftExact
    | rightExact =
  cong suc (cong₂ _+_ leftExact rightExact)

------------------------------------------------------------------------
-- Explicit work for all truth-table rows in every supplied restriction node.
------------------------------------------------------------------------

rootedNodeEvaluationWork :
  ∀ {rootVariables remaining : Nat}
    {root : SAT.BooleanFormula rootVariables} →
  List (Width.LayerNode {root = root} remaining) →
  Nat
rootedNodeEvaluationWork {remaining = remaining} [] =
  zero
rootedNodeEvaluationWork {remaining = remaining} (node ∷ rest) =
  Bits.bitCardinality remaining *
    formulaNodeVisits (Family.currentFormula (Width.node node))
  + rootedNodeEvaluationWork rest

rootedLayerEvaluationWork :
  ∀ {rootVariables remaining : Nat}
    {root : SAT.BooleanFormula rootVariables} →
  (path : Root.DescentPath root remaining) →
  Nat
rootedLayerEvaluationWork path =
  rootedNodeEvaluationWork (Root.rootedLayer path)

------------------------------------------------------------------------
-- A more accurate upper-envelope cost now adds structural evaluator visits
-- rather than pretending a row evaluation is constant cost. Remaining Q1
-- charges include assignment-index lookup, tree allocation, full graph
-- assembly and memory, quotient ID searches, terminal checks and direct-DP
-- operational recurrence overhead.
------------------------------------------------------------------------
