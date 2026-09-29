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

open import Agda.Builtin.Bool using (Bool)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Vec.Base using (Vec; []; _∷_)
open import Relation.Binary.PropositionalEquality using (cong; trans)

import DASHI.Mathematics.Complexity.CookLevinCircuitGCTBoundary as Cook
import DASHI.Mathematics.Complexity.BooleanFormulaSATSelfReductionExact as SAT
import DASHI.Mathematics.Complexity.PNotEqualsNPSemanticQuotientExponentialNoGoExact as Equality
import DASHI.Mathematics.Complexity.PNotEqualsNPBlockEqualityResidualWidthWitnessExact as Block
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
    (symBlockEvaluation left right)
  where
    symBlockEvaluation :
      ∀ {n : Nat}
        (xs ys : Vec Bool n) →
      Equality.vecEq xs ys
      ≡
      SAT.evaluate
        (Block.blockEqualityFormula n)
        (Block.blockAssignment xs ys)
    symBlockEvaluation xs ys
      with Block.blockEqualityEvaluation xs ys
    ... | refl = refl

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
-- This owner intentionally avoids a claim of SAT polynomial-time
-- decidability: block equality is an easy explicit family, not SAT.
------------------------------------------------------------------------
