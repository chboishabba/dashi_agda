module DASHI.Mathematics.Complexity.PNotEqualsNPStrictRepresentativeCircularityExact where

------------------------------------------------------------------------
-- STRICTLY SMALLER REPRESENTATIVES ARE TRIVIAL IF SAT TRUTH IS ALLOWED
--
-- Under SAT in P, every formula phi has the one-node representative:
--
--   if D(phi)=true  then constant true
--   if D(phi)=false then constant false.
--
-- Exactness of D proves this representative is equisatisfiable with phi.
--
-- Therefore for every formula with node count > 1, a strictly smaller semantic
-- representative exists trivially.
--
-- CONSEQUENCE:
--
-- "strict semantic representative" is useful only when its CONSTRUCTION is
-- independently derived from the special self-instantiation structure and does
-- not call D(phi) or another exact SAT solver on phi.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (_×_; _,_)
open import Agda.Builtin.Nat using (Nat; suc)
open import Data.Nat.Base using (_<_)
open import Relation.Binary.PropositionalEquality using (sym; trans)

import DASHI.Mathematics.Complexity.CookLevinCircuitGCTBoundary as Cook
import DASHI.Mathematics.Complexity.PolynomialReductionExact as PR
import DASHI.Mathematics.Complexity.PNotEqualsNPClayCoreExact as Clay
import DASHI.Mathematics.Complexity.PNotEqualsNPProgramDescriptionFormulaEmbeddingExact as Size

falseNotTrue : false ≡ true → ⊥
falseNotTrue ()

------------------------------------------------------------------------
-- Oracle-chosen one-node representative.
------------------------------------------------------------------------

oracleRepresentative :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula} →
  PR.InP cost Clay.SATLanguage →
  Cook.BooleanFormula →
  Cook.BooleanFormula
oracleRepresentative satP formula
    with PR.decide satP formula
... | true =
  Cook.constant true
... | false =
  Cook.constant false

oracleRepresentativeHasOneNode :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    (satP : PR.InP cost Clay.SATLanguage)
    (formula : Cook.BooleanFormula) →
  Size.formulaNodeCount
    (oracleRepresentative satP formula)
  ≡ suc 0
oracleRepresentativeHasOneNode satP formula
    with PR.decide satP formula
... | true = refl
... | false = refl

------------------------------------------------------------------------
-- Exact equisatisfiability.
------------------------------------------------------------------------

oracleRepresentativeEquivalent :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    (satP : PR.InP cost Clay.SATLanguage)
    (formula : Cook.BooleanFormula) →
  (Cook.Satisfiable formula →
    Cook.Satisfiable
      (oracleRepresentative satP formula))
  ×
  (Cook.Satisfiable
      (oracleRepresentative satP formula) →
    Cook.Satisfiable formula)
oracleRepresentativeEquivalent satP formula
    with PR.decide satP formula
... | true =
  forward
  ,
  backward
  where
    forward :
      Cook.Satisfiable formula →
      Cook.Satisfiable (Cook.constant true)
    forward satisfiable =
      Cook.satisfyingAssignment
        (λ index → false)
        refl

    backward :
      Cook.Satisfiable (Cook.constant true) →
      Cook.Satisfiable formula
    backward witness =
      PR.sound satP formula refl
... | false =
  forward
  ,
  backward
  where
    forward :
      Cook.Satisfiable formula →
      Cook.Satisfiable (Cook.constant false)
    forward satisfiable =
      ⊥-elim
        (falseNotTrue
          (PR.complete
            satP
            formula
            satisfiable))

    backward :
      Cook.Satisfiable (Cook.constant false) →
      Cook.Satisfiable formula
    backward
        (Cook.satisfyingAssignment
          assignment
          evaluatesTrue) =
      ⊥-elim
        (falseNotTrue evaluatesTrue)

------------------------------------------------------------------------
-- Every nontrivial formula therefore has a strict oracle-chosen representative.
------------------------------------------------------------------------

oracleRepresentativeStrictlySmaller :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    (satP : PR.InP cost Clay.SATLanguage)
    (formula : Cook.BooleanFormula) →
  suc 0 < Size.formulaNodeCount formula →
  Size.formulaNodeCount
    (oracleRepresentative satP formula)
  <
  Size.formulaNodeCount formula
oracleRepresentativeStrictlySmaller
    satP formula oneBelowFormula
    rewrite
      oracleRepresentativeHasOneNode
        satP formula =
  oneBelowFormula

------------------------------------------------------------------------
-- Research consequence.
--
-- The strong P9 target must NOT be advertised merely as:
--
--   "find a strictly smaller equisatisfiable representative".
--
-- That object is trivial under the contradiction hypothesis if its constructor
-- may inspect D(phi).
--
-- The actual theorem remains:
--
--   derive the representative from independently available structural data
--   WITHOUT evaluating D(phi), while keeping the representative strictly
--   smaller and preserving SAT truth.
------------------------------------------------------------------------
