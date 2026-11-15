module DASHI.Mathematics.Complexity.PNotEqualsNPFixedInstanceQuantifierNoGoExact where

------------------------------------------------------------------------
-- CLAY P != NP: EXACT QUANTIFIER NEGATIVE CONTROL.
--
-- The 2026-11-12 four-frontier attachment wrote
--
--   exists formula phi, for every polynomial-time decider D,
--     D(phi) differs from SAT(phi).
--
-- This incorrectly interchanges the quantifiers.  A constant decider can
-- agree with the SAT bit at any selected single formula, without solving
-- SAT on all formulas.  The correct target is
--
--   for every polynomial-time D, exists phi, D(phi) differs from SAT(phi).
--
-- The actual latter target is already owned by
-- PNotEqualsNPDirectSATLowerBoundExact.UniversalPolynomialSATDecisionFailure.
--
-- IMPORTANT: PolynomialCostModel does NOT require constant deciders to be
-- polynomial, so this theorem takes explicit certificates of both constant
-- algorithms in the very SAME cost model.  No axiom, unsafe flag, or
-- complexity-class completion is inferred from those certificates.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Data.Product using (Σ; _,_; proj₁; proj₂)

import DASHI.Mathematics.Complexity.CookLevinCircuitGCTBoundary as Cook
import DASHI.Mathematics.Complexity.PolynomialReductionExact as PR
import DASHI.Mathematics.Complexity.PNotEqualsNPDirectSATLowerBoundExact as Direct

record ConstantBooleanDeciderCost
    (cost : PR.PolynomialCostModel Cook.BooleanFormula) : Set₁ where
  field
    constantTruePolynomial :
      PR.polynomialTimeDecider cost (λ _ → true)
    constantFalsePolynomial :
      PR.polynomialTimeDecider cost (λ _ → false)

open ConstantBooleanDeciderCost public

constantTrueCandidate :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula} →
  ConstantBooleanDeciderCost cost →
  Direct.PolynomialSATDeciderCandidate cost
constantTrueCandidate certificates =
  Direct.polynomial-sat-decider-candidate
    (λ _ → true)
    (constantTruePolynomial certificates)

constantFalseCandidate :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula} →
  ConstantBooleanDeciderCost cost →
  Direct.PolynomialSATDeciderCandidate cost
constantFalseCandidate certificates =
  Direct.polynomial-sat-decider-candidate
    (λ _ → false)
    (constantFalsePolynomial certificates)

-- No decidability claim for a global SAT function is needed: truth is an
-- arbitrary Boolean reference classification.  The counterargument works
-- for SAT as soon as its standard decision bit is supplied.
pointwisePolynomialCandidateMatchesReference :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula} →
  (constants : ConstantBooleanDeciderCost cost) →
  (truth : Cook.BooleanFormula → Bool) →
  (formula : Cook.BooleanFormula) →
  Σ (Direct.PolynomialSATDeciderCandidate cost)
    (λ candidate → Direct.decide candidate formula ≡ truth formula)
pointwisePolynomialCandidateMatchesReference constants truth formula
    with truth formula
... | true = constantTrueCandidate constants , refl
... | false = constantFalseCandidate constants , refl

-- Refutes the attached exists-phi/forall-machine universal disagreement
-- for any cost model that admits both standard constant-time deciders.
-- Does NOT produce a decider correct on all formulas.
singleFormulaCannotDefeatEveryPolynomialCandidate :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula} →
  (constants : ConstantBooleanDeciderCost cost) →
  (truth : Cook.BooleanFormula → Bool) →
  (formula : Cook.BooleanFormula) →
  ((candidate : Direct.PolynomialSATDeciderCandidate cost) →
    Direct.decide candidate formula ≡ truth formula → ⊥) →
  ⊥
singleFormulaCannotDefeatEveryPolynomialCandidate
    constants truth formula impossible =
  impossible
    (proj₁ (pointwisePolynomialCandidateMatchesReference
      constants truth formula))
    (proj₂ (pointwisePolynomialCandidateMatchesReference
      constants truth formula))

-- In contrast, an algorithm-dependent counterexample formula is the
-- correct (forall-machine/exists-formula) shape. The witnesses themselves
-- remain an unpaid P != NP mathematical lower-bound problem.
UniversalWrongAtSomeFormula :
  (cost : PR.PolynomialCostModel Cook.BooleanFormula) →
  (truth : Cook.BooleanFormula → Bool) →
  Set₁
UniversalWrongAtSomeFormula cost truth =
  (candidate : Direct.PolynomialSATDeciderCandidate cost) →
  Σ Cook.BooleanFormula
    (λ formula → Direct.decide candidate formula ≡ truth formula → ⊥)
