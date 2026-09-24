module DASHI.Mathematics.Complexity.PNotEqualsNPGlobalTruthQuotientFirewallExact where

------------------------------------------------------------------------
-- GLOBAL TWO-CLASS TRUTH QUOTIENT FIREWALL
--
-- If a Boolean classifier Q on ALL Cook formulas satisfies
--
--   Q(phi) = Q(psi)
--      ->
--   SAT(phi) <-> SAT(psi),
--
-- then the known satisfiable/unsatisfiable anchors force opposite Q values.
-- Because Bool has only two values, Q is extensionally either:
--
--   SAT characteristic function,
--
-- or its complement.
--
-- Thus a cheap GLOBAL two-class truth-preserving quotient merely renames an
-- exact SAT decision procedure up to orientation.  P9 must therefore remain
-- scoped to the special self-diagonal restriction family.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (_×_; _,_; proj₁)
open import Relation.Binary.PropositionalEquality using (sym; trans)

import DASHI.Mathematics.Complexity.CookLevinCircuitGCTBoundary as Cook
import DASHI.Mathematics.Complexity.PolynomialReductionExact as PR
import DASHI.Mathematics.Complexity.PNotEqualsNPClayCoreExact as Clay
import DASHI.Mathematics.Complexity.PNotEqualsNPDirectSATLowerBoundExact as Direct

falseNotTrue : false ≡ true → ⊥
falseNotTrue ()

------------------------------------------------------------------------
-- Global truth-preserving Boolean quotient.
------------------------------------------------------------------------

SatisfiabilityEquivalent :
  Cook.BooleanFormula →
  Cook.BooleanFormula →
  Set
SatisfiabilityEquivalent left right =
  (Cook.Satisfiable left → Cook.Satisfiable right)
  ×
  (Cook.Satisfiable right → Cook.Satisfiable left)

record GlobalBooleanTruthQuotient : Set₁ where
  constructor global-boolean-truth-quotient
  field
    classify :
      Cook.BooleanFormula →
      Bool

    sameClassImpliesSatisfiabilityEquivalent :
      ∀ left right →
      classify left ≡ classify right →
      SatisfiabilityEquivalent left right

open GlobalBooleanTruthQuotient public

------------------------------------------------------------------------
-- Anchors must lie in opposite classes.
------------------------------------------------------------------------

anchorsCannotShareClass :
  (quotient : GlobalBooleanTruthQuotient) →
  classify quotient Cook.excludedMiddleFormula
  ≡ classify quotient Direct.contradictionFormula →
  ⊥
anchorsCannotShareClass quotient same =
  Direct.contradictionFormulaIsUnsatisfiable
    (forward
      Cook.excludedMiddleFormulaIsSatisfiable)
  where
    equivalence :
      SatisfiabilityEquivalent
        Cook.excludedMiddleFormula
        Direct.contradictionFormula
    equivalence =
      sameClassImpliesSatisfiabilityEquivalent
        quotient
        Cook.excludedMiddleFormula
        Direct.contradictionFormula
        same

    forward :
      Cook.Satisfiable Cook.excludedMiddleFormula →
      Cook.Satisfiable Direct.contradictionFormula
    forward =
      proj₁ equivalence

------------------------------------------------------------------------
-- If the satisfiable anchor is class true, Q itself decides SAT exactly.
------------------------------------------------------------------------

trueOrientedSound :
  (quotient : GlobalBooleanTruthQuotient) →
  classify quotient Cook.excludedMiddleFormula ≡ true →
  (formula : Cook.BooleanFormula) →
  classify quotient formula ≡ true →
  Cook.Satisfiable formula
trueOrientedSound quotient anchorTrue formula formulaTrue =
  proj₁
    (sameClassImpliesSatisfiabilityEquivalent
      quotient
      Cook.excludedMiddleFormula
      formula
      (trans anchorTrue (sym formulaTrue)))
    Cook.excludedMiddleFormulaIsSatisfiable

trueOrientedComplete :
  (quotient : GlobalBooleanTruthQuotient) →
  classify quotient Cook.excludedMiddleFormula ≡ true →
  (formula : Cook.BooleanFormula) →
  Cook.Satisfiable formula →
  classify quotient formula ≡ true
trueOrientedComplete quotient anchorTrue formula satisfiable
    with classify quotient formula
... | true =
  refl
... | false =
  ⊥-elim
    (Direct.contradictionFormulaIsUnsatisfiable
      (proj₁
        (sameClassImpliesSatisfiabilityEquivalent
          quotient
          formula
          Direct.contradictionFormula
          sameFalseClass)
        satisfiable))
  where
    contradictionFalse :
      classify quotient Direct.contradictionFormula
      ≡ false
    contradictionFalse
      with classify quotient Direct.contradictionFormula
    ... | false = refl
    ... | true =
      ⊥-elim
        (anchorsCannotShareClass
          quotient
          (trans anchorTrue refl))

    sameFalseClass :
      classify quotient formula
      ≡ classify quotient Direct.contradictionFormula
    sameFalseClass =
      trans refl (sym contradictionFalse)

------------------------------------------------------------------------
-- If the satisfiable anchor is class false, Q is the complemented SAT bit:
-- satisfiable formulas are exactly class false.
------------------------------------------------------------------------

falseOrientedSound :
  (quotient : GlobalBooleanTruthQuotient) →
  classify quotient Cook.excludedMiddleFormula ≡ false →
  (formula : Cook.BooleanFormula) →
  classify quotient formula ≡ false →
  Cook.Satisfiable formula
falseOrientedSound quotient anchorFalse formula formulaFalse =
  proj₁
    (sameClassImpliesSatisfiabilityEquivalent
      quotient
      Cook.excludedMiddleFormula
      formula
      (trans anchorFalse (sym formulaFalse)))
    Cook.excludedMiddleFormulaIsSatisfiable

falseOrientedComplete :
  (quotient : GlobalBooleanTruthQuotient) →
  classify quotient Cook.excludedMiddleFormula ≡ false →
  (formula : Cook.BooleanFormula) →
  Cook.Satisfiable formula →
  classify quotient formula ≡ false
falseOrientedComplete quotient anchorFalse formula satisfiable
    with classify quotient formula
... | false =
  refl
... | true =
  ⊥-elim
    (Direct.contradictionFormulaIsUnsatisfiable
      (proj₁
        (sameClassImpliesSatisfiabilityEquivalent
          quotient
          formula
          Direct.contradictionFormula
          sameTrueClass)
        satisfiable))
  where
    contradictionTrue :
      classify quotient Direct.contradictionFormula
      ≡ true
    contradictionTrue
      with classify quotient Direct.contradictionFormula
    ... | true = refl
    ... | false =
      ⊥-elim
        (anchorsCannotShareClass
          quotient
          (trans anchorFalse refl))

    sameTrueClass :
      classify quotient formula
      ≡ classify quotient Direct.contradictionFormula
    sameTrueClass =
      trans refl (sym contradictionTrue)

------------------------------------------------------------------------
-- If a true-oriented global classifier is polynomial, it literally yields
-- SAT in P using the SAME classifier and SAME polynomial certificate.
------------------------------------------------------------------------

trueOrientedPolynomialGlobalQuotientGivesSATInP :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula} →
  (quotient : GlobalBooleanTruthQuotient) →
  classify quotient Cook.excludedMiddleFormula ≡ true →
  PR.polynomialTimeDecider cost (classify quotient) →
  PR.InP cost Clay.SATLanguage
trueOrientedPolynomialGlobalQuotientGivesSATInP
    quotient anchorTrue polynomial =
  record
    { PR.decide =
        classify quotient
    ; PR.sound =
        trueOrientedSound
          quotient
          anchorTrue
    ; PR.complete =
        trueOrientedComplete
          quotient
          anchorTrue
    ; PR.polynomialDecision =
        polynomial
    }

------------------------------------------------------------------------
-- Research consequence.
--
-- A global two-state quotient is not the P9 breakthrough:
--
--   * if true-oriented, it is literally a SAT decider;
--   * if false-oriented, it is the complement orientation.
--
-- The route must classify only the SPECIAL self-diagonal restriction family,
-- from independently derivable intensional structure, and then use that local
-- state recurrence to close the bounded fixed point.
------------------------------------------------------------------------
