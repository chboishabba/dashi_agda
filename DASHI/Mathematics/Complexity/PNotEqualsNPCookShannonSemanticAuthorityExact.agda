module DASHI.Mathematics.Complexity.PNotEqualsNPCookShannonSemanticAuthorityExact where

------------------------------------------------------------------------
-- SHANNON SEMANTIC AUTHORITY ON THE CLAY-CRITICAL COOK FORMULA LINEAGE
--
-- Bridge owner:
--   PNotEqualsNPCookIndexedFormulaBridgeExact
--
-- Shannon owner:
--   PNotEqualsNPSATShannonSemanticAuthorityExact
--
-- This file composes them.
--
-- Under the contradiction hypothesis SAT in P, every finite indexed formula
-- phi satisfies
--
--   D(indexedToCook phi)
--     =
--   D(indexedToCook (phi|0))
--     OR
--   D(indexedToCook (phi|1)).
--
-- For an ordinary Cook formula with a supplied positive finite variable bound,
-- Cook -> indexed -> Cook is syntactically exact, so the root is the ORIGINAL
-- Cook formula rather than a parallel encoding.
--
-- This pays the representation seam required before P9 can be advertised as a
-- semantic quotient of the actual self-diagonal formula lineage.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; suc)
open import Relation.Binary.PropositionalEquality using (sym; trans)

import DASHI.Mathematics.Complexity.CookLevinCircuitGCTBoundary as Cook
import DASHI.Mathematics.Complexity.BooleanFormulaSATSelfReductionExact as SAT
import DASHI.Mathematics.Complexity.SATDecisionToWitnessSelfReductionExact as Search
import DASHI.Mathematics.Complexity.PolynomialReductionExact as PR
import DASHI.Mathematics.Complexity.PNotEqualsNPClayCoreExact as Clay
import DASHI.Mathematics.Complexity.PNotEqualsNPCookIndexedFormulaBridgeExact as Bridge
import DASHI.Mathematics.Complexity.PNotEqualsNPSATShannonSemanticAuthorityExact as Shannon

------------------------------------------------------------------------
-- Exact Shannon law after translating an indexed formula back to Cook syntax.
------------------------------------------------------------------------

cookDecisionShannonOnIndexed :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    (satP : PR.InP cost Clay.SATLanguage) →
  ∀ {variables : Nat}
    (formula : SAT.BooleanFormula (suc variables)) →
  PR.decide satP
    (Bridge.indexedToCook formula)
  ≡
  SAT.orBool
    (PR.decide satP
      (Bridge.indexedToCook
        (SAT.restrictHead false formula)))
    (PR.decide satP
      (Bridge.indexedToCook
        (SAT.restrictHead true formula)))
cookDecisionShannonOnIndexed
    satP formula =
  Shannon.satDecisionShannon
    (Bridge.indexedOracleFromCookInP satP)
    formula

------------------------------------------------------------------------
-- Same theorem beginning from an ordinary Cook formula.
--
-- The caller provides an explicit positive bound witness:
--
--   VariablesBelow (suc variables) formula.
--
-- This is exactly the information needed to expose a head variable in the
-- indexed carrier.  No renumbering or formula replacement occurs.
------------------------------------------------------------------------

cookDecisionShannonWithPositiveBound :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    (satP : PR.InP cost Clay.SATLanguage)
    {variables : Nat}
    (formula : Cook.BooleanFormula)
    (below :
      Bridge.VariablesBelow
        (suc variables)
        formula) →
  PR.decide satP formula
  ≡
  SAT.orBool
    (PR.decide satP
      (Bridge.indexedToCook
        (SAT.restrictHead false
          (Bridge.cookToIndexedWithBound
            formula
            below))))
    (PR.decide satP
      (Bridge.indexedToCook
        (SAT.restrictHead true
          (Bridge.cookToIndexedWithBound
            formula
            below))))
cookDecisionShannonWithPositiveBound
    satP formula below =
  trans
    (congruenceRoot
      (Bridge.indexedAfterCookWithBound
        formula
        below))
    (cookDecisionShannonOnIndexed
      satP
      (Bridge.cookToIndexedWithBound
        formula
        below))
  where
    congruenceRoot :
      ∀ {left right : Cook.BooleanFormula} →
      left ≡ right →
      PR.decide satP right
      ≡ PR.decide satP left
    congruenceRoot refl =
      refl

------------------------------------------------------------------------
-- The two restricted Cook children are ordinary Clay-carrier formulas.
------------------------------------------------------------------------

cookFalseRestriction :
  ∀ {variables : Nat}
    (formula : Cook.BooleanFormula) →
  Bridge.VariablesBelow
    (suc variables)
    formula →
  Cook.BooleanFormula
cookFalseRestriction formula below =
  Bridge.indexedToCook
    (SAT.restrictHead false
      (Bridge.cookToIndexedWithBound
        formula below))

cookTrueRestriction :
  ∀ {variables : Nat}
    (formula : Cook.BooleanFormula) →
  Bridge.VariablesBelow
    (suc variables)
    formula →
  Cook.BooleanFormula
cookTrueRestriction formula below =
  Bridge.indexedToCook
    (SAT.restrictHead true
      (Bridge.cookToIndexedWithBound
        formula below))

------------------------------------------------------------------------
-- Research consequence.
--
-- The first genuine SAT-specific semantic recursion is now attached to the
-- same BooleanFormula carrier used by SATLowerBoundProducer and
-- SelfDiagonalSemanticWitness.
--
-- What remains missing for P9 is not a syntax bridge.  It is a special,
-- non-circular quotient/decomposition theorem for the restricted CHILDREN of
-- the constructed self-diagonal formula.
------------------------------------------------------------------------
