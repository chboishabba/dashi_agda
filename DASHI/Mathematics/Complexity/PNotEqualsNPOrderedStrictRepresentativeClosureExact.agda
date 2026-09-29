module DASHI.Mathematics.Complexity.PNotEqualsNPOrderedStrictRepresentativeClosureExact where

------------------------------------------------------------------------
-- VARIABLE ORDER + STRICT REPRESENTATIVE QUOTIENT
--
-- A successful P9 route may need to choose a good variable/decomposition order
-- before building its quotient.
--
-- This owner proves that the ordering step is semantically and resource safe:
--
--   * exact SAT decision is unchanged by a proved variable permutation;
--   * a strict representative quotient on the reordered root therefore gives
--     the original root decision from a smaller representative;
--   * the representative remains strictly smaller than the ORIGINAL root
--     because reordering preserves syntax-node count.
--
-- Thus the open theorem may jointly construct:
--
--   good order + small quotient + strict representatives.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥)
open import Data.Product using (proj₁; proj₂)
open import Data.Nat.Base using (_<_)
open import Relation.Binary.PropositionalEquality using (sym; trans)

import DASHI.Mathematics.Complexity.CookLevinCircuitGCTBoundary as Cook
import DASHI.Mathematics.Complexity.BooleanFormulaSATSelfReductionExact as SAT
import DASHI.Mathematics.Complexity.SATDecisionToWitnessSelfReductionExact as Search
import DASHI.Mathematics.Complexity.PolynomialReductionExact as PR
import DASHI.Mathematics.Complexity.PNotEqualsNPClayCoreExact as Clay
import DASHI.Mathematics.Complexity.PNotEqualsNPCookIndexedFormulaBridgeExact as Bridge
import DASHI.Mathematics.Complexity.PNotEqualsNPProgramDescriptionFormulaEmbeddingExact as Size
import DASHI.Mathematics.Complexity.PNotEqualsNPIndexedFormulaVariableReorderingExact as Reorder
import DASHI.Mathematics.Complexity.PNotEqualsNPResourceClosingRestrictionQuotientExact as Quotient
import DASHI.Mathematics.Complexity.PNotEqualsNPStrictSemanticRepresentativeQuotientExact as Strict
import DASHI.Mathematics.Complexity.PNotEqualsNPSelfDiagonalRestrictionFamilyExact as Family

falseNotTrue : false ≡ true → ⊥
falseNotTrue ()

------------------------------------------------------------------------
-- Exact SAT decision is invariant under variable permutation.
------------------------------------------------------------------------

decisionPreservedByReordering :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    (satP : PR.InP cost Clay.SATLanguage)
    {variables : Nat}
    (permutation : Reorder.VariablePermutation variables)
    (formula : SAT.BooleanFormula variables) →
  PR.decide satP
    (Bridge.indexedToCook formula)
  ≡
  PR.decide satP
    (Bridge.indexedToCook
      (Reorder.renameByPermutation
        permutation
        formula))
decisionPreservedByReordering
    satP
    permutation
    formula
    with PR.decide satP
           (Bridge.indexedToCook formula)
       | PR.decide satP
           (Bridge.indexedToCook
             (Reorder.renameByPermutation
               permutation
               formula))
... | true | true =
  refl
... | false | false =
  refl
... | true | false =
  falseNotTrue
    (PR.complete
      satP
      reorderedCook
      (Bridge.indexedSatisfyingGivesCookSatisfiable
        reordered
        (Reorder.permutationPreservesSatisfiabilityForward
          permutation
          formula
          originalSat)))
  where
    originalSat :
      SAT.Satisfying formula
    originalSat =
      Bridge.cookSatisfiableIndexedFormulaGivesIndexedSatisfying
        formula
        (PR.sound
          satP
          (Bridge.indexedToCook formula)
          refl)

    reordered :
      SAT.BooleanFormula variables
    reordered =
      Reorder.renameByPermutation
        permutation
        formula

    reorderedCook :
      Cook.BooleanFormula
    reorderedCook =
      Bridge.indexedToCook reordered
... | false | true =
  falseNotTrue
    (PR.complete
      satP
      (Bridge.indexedToCook formula)
      (Bridge.indexedSatisfyingGivesCookSatisfiable
        formula
        (Reorder.permutationPreservesSatisfiabilityBackward
          permutation
          formula
          reorderedSat)))
  where
    reordered :
      SAT.BooleanFormula variables
    reordered =
      Reorder.renameByPermutation
        permutation
        formula

    reorderedSat :
      SAT.Satisfying reordered
    reorderedSat =
      Bridge.cookSatisfiableIndexedFormulaGivesIndexedSatisfying
        reordered
        (PR.sound
          satP
          (Bridge.indexedToCook reordered)
          refl)

------------------------------------------------------------------------
-- A strict quotient on the reordered root gives strict descent for the
-- original root decision.
------------------------------------------------------------------------

orderedStrictRepresentativeDecision :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    (satP : PR.InP cost Clay.SATLanguage)
    {variables : Nat}
    (permutation : Reorder.VariablePermutation variables)
    (formula : SAT.BooleanFormula variables)
    (strictQuotient :
      Strict.StrictSemanticRepresentativeQuotient
        (Reorder.renameByPermutation
          permutation
          formula)) →
  PR.decide satP
    (Bridge.indexedToCook formula)
  ≡
  PR.decide satP
    (Strict.representative
      strictQuotient
      (Quotient.classify
        (Strict.quotient strictQuotient)
        Family.restrictionRoot))
orderedStrictRepresentativeDecision
    satP
    permutation
    formula
    strictQuotient =
  trans
    (decisionPreservedByReordering
      satP
      permutation
      formula)
    (Strict.rootDecisionStrictlyDescends
      satP
      strictQuotient)

orderedRootRepresentativeStrictlySmaller :
  ∀ {variables : Nat}
    (permutation : Reorder.VariablePermutation variables)
    (formula : SAT.BooleanFormula variables)
    (strictQuotient :
      Strict.StrictSemanticRepresentativeQuotient
        (Reorder.renameByPermutation
          permutation
          formula)) →
  Size.formulaNodeCount
    (Strict.representative
      strictQuotient
      (Quotient.classify
        (Strict.quotient strictQuotient)
        Family.restrictionRoot))
  <
  Size.formulaNodeCount
    (Bridge.indexedToCook formula)
orderedRootRepresentativeStrictlySmaller
    permutation
    formula
    strictQuotient
    rewrite
      sym
        (Reorder.reorderingPreservesCookNodeCount
          permutation
          formula) =
  Strict.rootRepresentativeIsStrictlySmaller
    strictQuotient

------------------------------------------------------------------------
-- Research consequence.
--
-- The current strongest non-circular P9 target may legitimately include an
-- order-selection theorem:
--
--   special self-instantiation structure
--        -> good variable order
--        -> finite semantic quotient
--        -> strictly smaller representatives
--        -> exact root decision from smaller D queries.
--
-- Neither SAT truth nor syntax size is changed by the ordering step.
------------------------------------------------------------------------
