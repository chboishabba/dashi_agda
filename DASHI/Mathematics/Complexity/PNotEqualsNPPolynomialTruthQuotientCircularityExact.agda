module DASHI.Mathematics.Complexity.PNotEqualsNPPolynomialTruthQuotientCircularityExact where

------------------------------------------------------------------------
-- UNDER SAT in P, A POLYNOMIAL TWO-CLASS TRUTH QUOTIENT IS TRIVIAL
--
-- Clay-critical correction for P9.
--
-- Assume the contradiction hypothesis:
--
--   satP : SAT in P.
--
-- Then the hypothesized polynomial-time exact SAT decider itself gives
--
--   Q(phi) := decide(phi) : Bool.
--
-- This quotient has:
--
--   * exactly a one-bit / at-most-two-class codomain;
--   * polynomial-time construction, by the same certificate as satP;
--   * exact truth soundness:
--
--       Q(phi) = Q(psi)
--          =>
--       SAT(phi) <-> SAT(psi).
--
-- Therefore "small image + truth preservation + polynomial classifier" is NOT
-- a useful contradiction step.  It is already implied by the hypothesis we
-- are trying to refute.
--
-- The surviving P9 requirement must be stronger:
--
--   derive the quotient WITHOUT invoking the target SAT decision procedure
--   (or any equivalent exact SAT computation) on the restricted instance.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (sym; trans)

import DASHI.Mathematics.Complexity.CookLevinCircuitGCTBoundary as Cook
import DASHI.Mathematics.Complexity.PolynomialReductionExact as PR
import DASHI.Mathematics.Complexity.PNotEqualsNPClayCoreExact as Clay

falseNotTrue : false ≡ true → ⊥
falseNotTrue ()

------------------------------------------------------------------------
-- Truth equivalence on ordinary Cook BooleanFormula instances.
------------------------------------------------------------------------

SatisfiabilityEquivalent :
  Cook.BooleanFormula →
  Cook.BooleanFormula →
  Set
SatisfiabilityEquivalent left right =
  (Cook.Satisfiable left → Cook.Satisfiable right)
  ×
  (Cook.Satisfiable right → Cook.Satisfiable left)

------------------------------------------------------------------------
-- The hypothetical SAT decider is itself the quotient classifier.
------------------------------------------------------------------------

polynomialTruthClass :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula} →
  PR.InP cost Clay.SATLanguage →
  Cook.BooleanFormula →
  Bool
polynomialTruthClass satP =
  PR.decide satP

polynomialTruthClassIsPolynomial :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    (satP : PR.InP cost Clay.SATLanguage) →
  PR.polynomialTimeDecider
    cost
    (polynomialTruthClass satP)
polynomialTruthClassIsPolynomial satP =
  PR.polynomialDecision satP

------------------------------------------------------------------------
-- Same class bit gives exact equisatisfiability.
------------------------------------------------------------------------

samePolynomialTruthClassImpliesSatisfiabilityEquivalent :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    (satP : PR.InP cost Clay.SATLanguage)
    (left right : Cook.BooleanFormula) →
  polynomialTruthClass satP left
  ≡ polynomialTruthClass satP right →
  SatisfiabilityEquivalent left right
samePolynomialTruthClassImpliesSatisfiabilityEquivalent
    satP left right same
    with polynomialTruthClass satP left
       | polynomialTruthClass satP right
       | same
... | true | true | refl =
  (λ leftSat →
    PR.sound satP right refl)
  ,
  (λ rightSat →
    PR.sound satP left refl)
... | false | false | refl =
  impossibleLeft
  ,
  impossibleRight
  where
    impossibleLeft :
      Cook.Satisfiable left →
      Cook.Satisfiable right
    impossibleLeft leftSat =
      ⊥-elim
        (falseNotTrue
          (PR.complete
            satP
            left
            leftSat))

    impossibleRight :
      Cook.Satisfiable right →
      Cook.Satisfiable left
    impossibleRight rightSat =
      ⊥-elim
        (falseNotTrue
          (PR.complete
            satP
            right
            rightSat))

------------------------------------------------------------------------
-- Definitional circularity boundary.
------------------------------------------------------------------------

truthClassIsHypotheticalSATDecision :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    (satP : PR.InP cost Clay.SATLanguage)
    (formula : Cook.BooleanFormula) →
  polynomialTruthClass satP formula
  ≡ PR.decide satP formula
truthClassIsHypotheticalSATDecision satP formula =
  refl

------------------------------------------------------------------------
-- Research consequence.
--
-- Under the contradiction hypothesis SAT in P, obligations
--
--   (2) equal quotient => equal SAT truth,
--   (3) tiny quotient image,
--   (4) polynomial quotient construction
--
-- can all be paid trivially by Q = D.
--
-- Hence the mathematically nontrivial P9 condition is obligation (1):
--
--   Q must be derived from independently available intensional/self-instance
--   structure without calling D on that restricted instance or performing an
--   equivalent exact SAT decision.
--
-- Any future P9 owner should expose that provenance/resource restriction
-- explicitly; otherwise it merely repackages SAT in P.
------------------------------------------------------------------------
