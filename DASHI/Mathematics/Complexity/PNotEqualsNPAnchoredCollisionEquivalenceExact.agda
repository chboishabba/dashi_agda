module DASHI.Mathematics.Complexity.PNotEqualsNPAnchoredCollisionEquivalenceExact where

------------------------------------------------------------------------
-- ANCHORED COLLISION = UNIVERSAL CONCRETE SAT DECISION FAILURE
--
-- This is a max-cut compression theorem, not a new P != NP assumption.
--
-- `PNotEqualsNPDirectSATLowerBoundExact` already proves:
--
--   * every arbitrary polynomial SAT candidate is either anchored or already
--     carries a concrete SAT decision failure;
--   * on an anchored candidate, a SAT/UNSAT same-output collision gives a
--     concrete decision failure;
--   * conversely, a concrete failure of an anchored candidate gives such a
--     collision.
--
-- Therefore the two universal open theorem families are constructively
-- interderivable.  The anchored-collision wording is useful for observer /
-- non-descent mechanisms, but it is not a stronger mathematical leaf than
-- universal concrete SAT failure.
------------------------------------------------------------------------

open import Data.Sum.Base using (inj₁; inj₂)

import DASHI.Mathematics.Complexity.CookLevinCircuitGCTBoundary as Cook
import DASHI.Mathematics.Complexity.PolynomialReductionExact as PR
import DASHI.Mathematics.Complexity.PNotEqualsNPDirectSATLowerBoundExact as Direct

universalDecisionFailureGivesAnchoredCollision :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula} →
  Direct.UniversalPolynomialSATDecisionFailure cost →
  Direct.UniversalAnchoredPolynomialSATDecisionCollision cost
universalDecisionFailureGivesAnchoredCollision universalFailure anchored =
  Direct.decisionFailureGivesAnchoredCollision
    (universalFailure (Direct.candidate anchored))

universalAnchoredCollisionGivesUniversalDecisionFailure :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula} →
  Direct.UniversalAnchoredPolynomialSATDecisionCollision cost →
  Direct.UniversalPolynomialSATDecisionFailure cost
universalAnchoredCollisionGivesUniversalDecisionFailure
    universalCollision candidate
    with Direct.candidateIsAnchoredOrAlreadyFails candidate
... | inj₁ anchored =
  Direct.collisionGivesDecisionFailure
    (universalCollision anchored)
... | inj₂ failure = failure

------------------------------------------------------------------------
-- Paired receipt: both directions are theorem terms on the literal SAT
-- candidate/error/collision carriers.
------------------------------------------------------------------------

record UniversalSATFailureCollisionEquivalence
    (cost : PR.PolynomialCostModel Cook.BooleanFormula) : Set₁ where
  constructor universal-sat-failure-collision-equivalence
  field
    failureToCollision :
      Direct.UniversalPolynomialSATDecisionFailure cost →
      Direct.UniversalAnchoredPolynomialSATDecisionCollision cost

    collisionToFailure :
      Direct.UniversalAnchoredPolynomialSATDecisionCollision cost →
      Direct.UniversalPolynomialSATDecisionFailure cost

universalSATFailureCollisionEquivalence :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula} →
  UniversalSATFailureCollisionEquivalence cost
universalSATFailureCollisionEquivalence =
  universal-sat-failure-collision-equivalence
    universalDecisionFailureGivesAnchoredCollision
    universalAnchoredCollisionGivesUniversalDecisionFailure
