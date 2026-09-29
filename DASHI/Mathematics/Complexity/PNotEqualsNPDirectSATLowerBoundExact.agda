module DASHI.Mathematics.Complexity.PNotEqualsNPDirectSATLowerBoundExact where

------------------------------------------------------------------------
-- DIRECT SAT LOWER-BOUND RESEARCH SURFACE
--
-- This file lies on the Clay-critical dependency path:
--
--   universal polynomial SAT failure/collision
--        -> SATNotInP
--        -> SATLowerBoundProducer
--        -> P != NP.
--
-- It deliberately does not introduce another complexity-class boundary.
-- The only open theorem families below quantify over every candidate already
-- certified polynomial-time by the repository's PolynomialCostModel.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (zero)
open import Data.Empty using (⊥)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (sym; trans)

import DASHI.Mathematics.Complexity.CookLevinCircuitGCTBoundary as Cook
import DASHI.Mathematics.Complexity.PolynomialReductionExact as PR
import DASHI.Mathematics.Complexity.PNotEqualsNPClayCoreExact as Clay

falseNotTrue : false ≡ true → ⊥
falseNotTrue ()

absurd : ∀ {A : Set} → ⊥ → A
absurd ()

------------------------------------------------------------------------
-- Polynomial candidates: algorithm + polynomial-time certificate only.
-- Correctness is NOT included.
------------------------------------------------------------------------

record PolynomialSATDeciderCandidate
    (cost : PR.PolynomialCostModel Cook.BooleanFormula) : Set₁ where
  constructor polynomial-sat-decider-candidate
  field
    decide : Cook.BooleanFormula → Bool
    polynomialDecision :
      PR.polynomialTimeDecider cost decide

open PolynomialSATDeciderCandidate public

inPToPolynomialSATDeciderCandidate :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula} →
  PR.InP cost Clay.SATLanguage →
  PolynomialSATDeciderCandidate cost
inPToPolynomialSATDeciderCandidate satP =
  polynomial-sat-decider-candidate
    (PR.decide satP)
    (PR.polynomialDecision satP)

------------------------------------------------------------------------
-- Two fixed anchors orient the decision bit.
--
-- Cook already supplies x OR not-x as a satisfiable formula.  We add the
-- dual x AND not-x and prove directly that it is unsatisfiable.
------------------------------------------------------------------------

contradictionFormula : Cook.BooleanFormula
contradictionFormula =
  Cook.conjunction
    (Cook.variable zero)
    (Cook.negate (Cook.variable zero))

contradictionFormulaIsUnsatisfiable :
  Cook.Satisfiable contradictionFormula → ⊥
contradictionFormulaIsUnsatisfiable
    (Cook.satisfyingAssignment assignment evaluatesTrue)
    with assignment zero
... | true = falseNotTrue evaluatesTrue
... | false = falseNotTrue evaluatesTrue

record AnchoredPolynomialSATDeciderCandidate
    (cost : PR.PolynomialCostModel Cook.BooleanFormula) : Set₁ where
  constructor anchored-polynomial-sat-decider-candidate
  field
    candidate : PolynomialSATDeciderCandidate cost
    acceptsKnownSatisfiable :
      decide candidate Cook.excludedMiddleFormula ≡ true
    rejectsKnownUnsatisfiable :
      decide candidate contradictionFormula ≡ false

open AnchoredPolynomialSATDeciderCandidate public

inPToAnchoredPolynomialSATDeciderCandidate :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula} →
  PR.InP cost Clay.SATLanguage →
  AnchoredPolynomialSATDeciderCandidate cost
inPToAnchoredPolynomialSATDeciderCandidate satP =
  anchored-polynomial-sat-decider-candidate
    (inPToPolynomialSATDeciderCandidate satP)
    (PR.complete satP
      Cook.excludedMiddleFormula
      Cook.excludedMiddleFormulaIsSatisfiable)
    rejectsContradiction
  where
    rejectsContradiction :
      PR.decide satP contradictionFormula ≡ false
    rejectsContradiction with PR.decide satP contradictionFormula
    ... | true =
      absurd
        (contradictionFormulaIsUnsatisfiable
          (PR.sound satP contradictionFormula refl))
    ... | false = refl

------------------------------------------------------------------------
-- Concrete extensional failure modes.
------------------------------------------------------------------------

data SATDecisionFailure
    {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    (candidate : PolynomialSATDeciderCandidate cost) : Set₁ where

  falsePositive :
    (formula : Cook.BooleanFormula) →
    decide candidate formula ≡ true →
    (Cook.Satisfiable formula → ⊥) →
    SATDecisionFailure candidate

  falseNegative :
    (formula : Cook.BooleanFormula) →
    Cook.Satisfiable formula →
    decide candidate formula ≡ false →
    SATDecisionFailure candidate


------------------------------------------------------------------------
-- Anchoring is without loss for proof search.
--
-- Every polynomial candidate is constructively either:
--
--   * already wrong on one of the two fixed anchor formulas; or
--   * correctly oriented on both anchors.
--
-- Thus the hard theorem may restrict to anchored candidates without assuming
-- any unproved global SAT correctness.
------------------------------------------------------------------------

candidateIsAnchoredOrAlreadyFails :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    (candidate : PolynomialSATDeciderCandidate cost) →
  AnchoredPolynomialSATDeciderCandidate cost
  ⊎ SATDecisionFailure candidate
candidateIsAnchoredOrAlreadyFails candidate
    with decide candidate Cook.excludedMiddleFormula
       | decide candidate contradictionFormula
... | true | false =
  inj₁
    (anchored-polynomial-sat-decider-candidate
      candidate refl refl)
... | true | true =
  inj₂
    (falsePositive
      contradictionFormula
      refl
      contradictionFormulaIsUnsatisfiable)
... | false | false =
  inj₂
    (falseNegative
      Cook.excludedMiddleFormula
      Cook.excludedMiddleFormulaIsSatisfiable
      refl)
... | false | true =
  inj₂
    (falseNegative
      Cook.excludedMiddleFormula
      Cook.excludedMiddleFormulaIsSatisfiable
      refl)

failureContradictsCorrectSATDecision :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    (satP : PR.InP cost Clay.SATLanguage) →
  SATDecisionFailure (inPToPolynomialSATDeciderCandidate satP) →
  ⊥
failureContradictsCorrectSATDecision satP
    (falsePositive formula returnedTrue unsatisfiable) =
  unsatisfiable
    (PR.sound satP formula returnedTrue)

failureContradictsCorrectSATDecision satP
    (falseNegative formula satisfiable returnedFalse) =
  falseNotTrue
    (trans
      (sym returnedFalse)
      (PR.complete satP formula satisfiable))

------------------------------------------------------------------------
-- First direct open theorem family:
--
--   every polynomial-time Boolean candidate makes a concrete SAT error.
--
-- The explicit machine-time alternative from the human formulation has been
-- factored into PolynomialCostModel: this type quantifies only over algorithms
-- already certified polynomial-time in that model.
------------------------------------------------------------------------

UniversalPolynomialSATDecisionFailure :
  (cost : PR.PolynomialCostModel Cook.BooleanFormula) →
  Set₁
UniversalPolynomialSATDecisionFailure cost =
  (candidate : PolynomialSATDeciderCandidate cost) →
  SATDecisionFailure candidate

universalDecisionFailureGivesSATNotInP :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula} →
  UniversalPolynomialSATDecisionFailure cost →
  Clay.SATNotInP cost
universalDecisionFailureGivesSATNotInP universalFailure satP =
  failureContradictsCorrectSATDecision
    satP
    (universalFailure
      (inPToPolynomialSATDeciderCandidate satP))

universalDecisionFailureGivesSATLowerBoundProducer :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula} →
  UniversalPolynomialSATDecisionFailure cost →
  Clay.SATLowerBoundProducer cost
universalDecisionFailureGivesSATLowerBoundProducer universalFailure = record
  { Clay.satNotPolynomialTime =
      universalDecisionFailureGivesSATNotInP universalFailure
  }

universalDecisionFailureClosesPNotEqualsNP :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula} →
  Clay.PNotEqualsNPEstablishedBackground cost →
  UniversalPolynomialSATDecisionFailure cost →
  Clay.PNotEqualsNP cost
universalDecisionFailureClosesPNotEqualsNP background universalFailure =
  Clay.satLowerBoundProducerClosesClayCore
    background
    (universalDecisionFailureGivesSATLowerBoundProducer universalFailure)

------------------------------------------------------------------------
-- Collision mechanism, specialized all the way to the actual SAT decision bit.
--
-- The anchors matter.  Without them, a candidate computing the complement of
-- SAT separates satisfiable from unsatisfiable formulas without a same-output
-- collision, while still being wrong as a SAT decider.  Requiring correctness
-- only on one known satisfiable and one known unsatisfiable formula fixes the
-- orientation without assuming general SAT correctness.
------------------------------------------------------------------------

record SATDecisionCollision
    {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    (anchored : AnchoredPolynomialSATDeciderCandidate cost) : Set₁ where
  constructor sat-decision-collision
  field
    satisfiableFormula : Cook.BooleanFormula
    unsatisfiableFormula : Cook.BooleanFormula
    satisfiableWitness :
      Cook.Satisfiable satisfiableFormula
    unsatisfiableWitness :
      Cook.Satisfiable unsatisfiableFormula → ⊥
    sameDecision :
      decide (candidate anchored) satisfiableFormula
      ≡ decide (candidate anchored) unsatisfiableFormula

open SATDecisionCollision public

collisionGivesDecisionFailure :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {anchored : AnchoredPolynomialSATDeciderCandidate cost} →
  SATDecisionCollision anchored →
  SATDecisionFailure (candidate anchored)
collisionGivesDecisionFailure {anchored = anchored} collision
    with decide (candidate anchored) (satisfiableFormula collision)
       | decide (candidate anchored) (unsatisfiableFormula collision)
       | sameDecision collision
... | true | true | _ =
  falsePositive
    (unsatisfiableFormula collision)
    refl
    (unsatisfiableWitness collision)
... | true | false | ()
... | false | true | ()
... | false | false | _ =
  falseNegative
    (satisfiableFormula collision)
    (satisfiableWitness collision)
    refl

decisionFailureGivesAnchoredCollision :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {anchored : AnchoredPolynomialSATDeciderCandidate cost} →
  SATDecisionFailure (candidate anchored) →
  SATDecisionCollision anchored
decisionFailureGivesAnchoredCollision {anchored = anchored}
    (falsePositive formula returnedTrue unsatisfiable) =
  sat-decision-collision
    Cook.excludedMiddleFormula
    formula
    Cook.excludedMiddleFormulaIsSatisfiable
    unsatisfiable
    (trans
      (acceptsKnownSatisfiable anchored)
      (sym returnedTrue))
decisionFailureGivesAnchoredCollision {anchored = anchored}
    (falseNegative formula satisfiable returnedFalse) =
  sat-decision-collision
    formula
    contradictionFormula
    satisfiable
    contradictionFormulaIsUnsatisfiable
    (trans
      returnedFalse
      (sym (rejectsKnownUnsatisfiable anchored)))

------------------------------------------------------------------------
-- Second, stronger proof-search target:
--
--   every anchored polynomial SAT candidate has a satisfiable/unsatisfiable
--   same-output collision.
--
-- On anchored candidates this is exactly an error witness, by the two
-- compiler lemmas above.  This is the point at which the repository's
-- observer/non-descent method must pay its universal coverage debt.
------------------------------------------------------------------------

UniversalAnchoredPolynomialSATDecisionCollision :
  (cost : PR.PolynomialCostModel Cook.BooleanFormula) →
  Set₁
UniversalAnchoredPolynomialSATDecisionCollision cost =
  (anchored : AnchoredPolynomialSATDeciderCandidate cost) →
  SATDecisionCollision anchored

universalAnchoredCollisionGivesSATNotInP :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula} →
  UniversalAnchoredPolynomialSATDecisionCollision cost →
  Clay.SATNotInP cost
universalAnchoredCollisionGivesSATNotInP universalCollision satP =
  failureContradictsCorrectSATDecision
    satP
    (collisionGivesDecisionFailure
      (universalCollision
        (inPToAnchoredPolynomialSATDeciderCandidate satP)))

universalAnchoredCollisionGivesSATLowerBoundProducer :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula} →
  UniversalAnchoredPolynomialSATDecisionCollision cost →
  Clay.SATLowerBoundProducer cost
universalAnchoredCollisionGivesSATLowerBoundProducer universalCollision = record
  { Clay.satNotPolynomialTime =
      universalAnchoredCollisionGivesSATNotInP universalCollision
  }

universalAnchoredCollisionClosesPNotEqualsNP :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula} →
  Clay.PNotEqualsNPEstablishedBackground cost →
  UniversalAnchoredPolynomialSATDecisionCollision cost →
  Clay.PNotEqualsNP cost
universalAnchoredCollisionClosesPNotEqualsNP background universalCollision =
  Clay.satLowerBoundProducerClosesClayCore
    background
    (universalAnchoredCollisionGivesSATLowerBoundProducer universalCollision)
