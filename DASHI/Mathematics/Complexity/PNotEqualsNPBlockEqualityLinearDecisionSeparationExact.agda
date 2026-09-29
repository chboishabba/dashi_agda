module DASHI.Mathematics.Complexity.PNotEqualsNPBlockEqualityLinearDecisionSeparationExact where

------------------------------------------------------------------------
-- ALGORITHM-INDEPENDENCE TEST FOR ORDERED SEMANTIC WIDTH
--
-- The SAME literal blockEqualityFormula n:
--   * has 2^n pairwise distinct Shannon residuals in the BLOCK order
--     (existing BlockEqualityResidualWidthWitnessExact);
--   * admits a deterministic linear-time evaluator over its two input blocks.
--
-- The proof below is about the indexed formula's Boolean semantics, not
-- merely a different function that happens to have the same name.
--
-- Hence ordered residual width cannot be promoted to a lower bound on
-- arbitrary deterministic decision time, even for the SAME family.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Data.Nat.Base using (_≤_)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Vec.Base using (Vec; []; _∷_)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; subst; sym; trans)

import DASHI.Mathematics.Complexity.CookLevinCircuitGCTBoundary as Cook
import DASHI.Mathematics.Complexity.BooleanFormulaSATSelfReductionExact as SAT
import DASHI.Mathematics.Complexity.PNotEqualsNPSemanticQuotientExponentialNoGoExact as Equality
import DASHI.Mathematics.Complexity.PNotEqualsNPBlockEqualityResidualWidthWitnessExact as Block
import DASHI.Mathematics.Complexity.PNotEqualsNPIndexedFormulaVariableReorderingExact as Rename
import DASHI.Mathematics.Complexity.PNotEqualsNPQ1InstrumentedFormulaEvaluationExact as Eval
open import Data.Fin.Base using (Fin)
import DASHI.Mathematics.Complexity.PNotEqualsNPExactResidualSummaryBitLowerBoundExact as Bits
import DASHI.Mathematics.Complexity.PNotEqualsNPSelfDiagonalResidualWidthExact as Width

------------------------------------------------------------------------
-- One equality check per bit pair; eager recursion visits every pair.
-- Returned Nat is the ACTUAL recursive equality-check count.
------------------------------------------------------------------------

equalityDecisionWithCount :
  ∀ {width : Nat} →
  Vec Bool width →
  Vec Bool width →
  Bool × Nat
equalityDecisionWithCount [] [] =
  Cook.andBool true true , zero
equalityDecisionWithCount
    (left ∷ lefts)
    (right ∷ rights)
    with equalityDecisionWithCount lefts rights
... | answer , comparisons =
  Cook.andBool
    (Equality.boolEq left right)
    answer
  ,
  suc comparisons

------------------------------------------------------------------------
-- Decision semantics equal the repository's genuine vector equality.
------------------------------------------------------------------------

equalityDecisionValueExact :
  ∀ {width : Nat}
    (left right : Vec Bool width) →
  proj₁ (equalityDecisionWithCount left right)
  ≡
  Equality.vecEq left right
equalityDecisionValueExact [] [] =
  refl
equalityDecisionValueExact
    (left ∷ lefts)
    (right ∷ rights)
    with equalityDecisionWithCount lefts rights
       | equalityDecisionValueExact lefts rights
... | answer , comparisons | exact =
  cong (Cook.andBool (Equality.boolEq left right)) exact

------------------------------------------------------------------------
-- The actual evaluator makes EXACTLY width bit-pair comparisons.
------------------------------------------------------------------------

equalityDecisionCountExact :
  ∀ {width : Nat}
    (left right : Vec Bool width) →
  proj₂ (equalityDecisionWithCount left right)
  ≡ width
equalityDecisionCountExact [] [] =
  refl
equalityDecisionCountExact
    {suc width}
    (left ∷ lefts)
    (right ∷ rights)
    with equalityDecisionWithCount lefts rights
       | equalityDecisionCountExact lefts rights
... | answer , comparisons | exact =
  cong suc exact

------------------------------------------------------------------------
-- Same formula, same assignment, linear decision count. The existing
-- Block.blockEqualityResidualWidthWitness also uses precisely this formula.
------------------------------------------------------------------------

linearDecisionAgreesWithBlockEqualityFormula :
  ∀ {width : Nat}
    (left right : Vec Bool width) →
  proj₁ (equalityDecisionWithCount left right)
  ≡
  SAT.evaluate
    (Block.blockEqualityFormula width)
    (Block.blockAssignment left right)
linearDecisionAgreesWithBlockEqualityFormula left right =
  trans
    (equalityDecisionValueExact left right)
    (sym (Block.blockEqualityEvaluation left right))

------------------------------------------------------------------------
-- The SAME block-equality formula itself is linear in the bit width.
-- Renaming its variables never changes the syntax-node count.
------------------------------------------------------------------------

nodeVisitsInvariantUnderRenaming :
  ∀ {source target : Nat}
    (rename : Fin source → Fin target)
    (formula : SAT.BooleanFormula source) →
  Eval.formulaNodeVisits (Rename.renameFormula rename formula)
  ≡
  Eval.formulaNodeVisits formula
nodeVisitsInvariantUnderRenaming rename (SAT.variable index) =
  refl
nodeVisitsInvariantUnderRenaming rename (SAT.constant value) =
  refl
nodeVisitsInvariantUnderRenaming rename (SAT.negate formula) =
  cong suc (nodeVisitsInvariantUnderRenaming rename formula)
nodeVisitsInvariantUnderRenaming rename (SAT.conjunction left right) =
  cong suc
    (cong₂ _+_
      (nodeVisitsInvariantUnderRenaming rename left)
      (nodeVisitsInvariantUnderRenaming rename right))
nodeVisitsInvariantUnderRenaming rename (SAT.disjunction left right) =
  cong suc
    (cong₂ _+_
      (nodeVisitsInvariantUnderRenaming rename left)
      (nodeVisitsInvariantUnderRenaming rename right))

bitEqualityFormulaNodeVisits :
  ∀ {variables : Nat}
    (left right : Fin variables) →
  Eval.formulaNodeVisits (Block.bitEqualityFormula left right)
    ≡ 9
bitEqualityFormulaNodeVisits left right =
  refl

tenNodesPerEqualityPair : Nat → Nat
tenNodesPerEqualityPair zero = 1
tenNodesPerEqualityPair (suc width) =
  10 + tenNodesPerEqualityPair width

blockEqualityFormulaLinearSyntax :
  (width : Nat) →
  Eval.formulaNodeVisits (Block.blockEqualityFormula width)
  ≡
  tenNodesPerEqualityPair width
blockEqualityFormulaLinearSyntax zero =
  refl
blockEqualityFormulaLinearSyntax (suc width)
    rewrite
      bitEqualityFormulaNodeVisits
        (Block.leftBlock {left = suc width} {right = suc width} Fin.zero)
        (Block.rightBlock {left = suc width} {right = suc width} Fin.zero)
      |
      nodeVisitsInvariantUnderRenaming
        (Block.tailEmbedding {width = width})
        (Block.blockEqualityFormula width)
      |
      blockEqualityFormulaLinearSyntax width =
  refl

------------------------------------------------------------------------
-- Consequently, ordered exponential width persists for a SAME-FORMULA
-- family with a linear-size Boolean syntax tree and a linear-time direct
-- comparator. This does not establish an algorithm-independent SAT bound.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- A single certified donor simultaneously exhibits:
--
--   literal width 2^n under the block restriction order, AND
--   literal decision work n using ordinary input reading.
--
-- This disproves the proposed generic transfer
--   "ordered semantic width exponential => decision time exponential".
-- It does NOT disprove a richer candidate-coupled transfer theorem that
-- relies on independently proved, additional operational premises.
------------------------------------------------------------------------

sameFormulaWideYetLinear :
  (width : Nat) →
  Width.ResidualWidthWitness
    {root = Block.blockEqualityFormula width}
    width
    (Bits.bitCardinality width)
sameFormulaWideYetLinear =
  Block.blockEqualityResidualWidthWitness

------------------------------------------------------------------------
-- Direct formal counterinstance to the naive universal transfer
--
--     "2^n ordered residuals force at least 2^n decision comparisons".
--
-- At n=2: the WIDTH theorem supplies four residual classes, while the
-- actual evaluator uses precisely two comparisons on EVERY input.
------------------------------------------------------------------------

twoBitInput : Vec Bool (suc (suc zero))
twoBitInput = false ∷ false ∷ []

fourNotBelowTwo :
  Bits.bitCardinality (suc (suc zero))
  ≤
  suc (suc zero)
  →
  ⊥
fourNotBelowTwo ()

noOrderedWidthToDecisionCountTransfer :
  ((width : Nat)
   (left right : Vec Bool width) →
   Bits.bitCardinality width
   ≤
   proj₂ (equalityDecisionWithCount left right))
  →
  ⊥
noOrderedWidthToDecisionCountTransfer claimed =
  fourNotBelowTwo
    (subst
      (λ count →
        Bits.bitCardinality (suc (suc zero)) ≤ count)
      (equalityDecisionCountExact twoBitInput twoBitInput)
      (claimed
        (suc (suc zero))
        twoBitInput
        twoBitInput))

------------------------------------------------------------------------
-- This owner intentionally avoids a claim of SAT polynomial-time
-- decidability: block equality is an easy explicit family, not SAT.
------------------------------------------------------------------------
