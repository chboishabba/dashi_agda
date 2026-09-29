module DASHI.Mathematics.Complexity.PNotEqualsNPObserverCoverageExact where

------------------------------------------------------------------------
-- OBSERVER ROUTE -> DIRECT SAT COLLISION
--
-- This file places the existing PolynomialClassicalObserver machinery on the
-- actual P != NP dependency path without pretending it supplies a lower bound.
--
-- Given:
--   * an anchored polynomial SAT candidate D;
--   * a PolynomialClassicalObserver whose consumer is exactly D;
--   * one satisfiable and one unsatisfiable formula with the SAME observer
--     representation;
--
-- the observer factorization forces D to return the same bit on both formulas,
-- hence the direct SAT-collision theorem closes the candidate.
--
-- The unpaid theorem is therefore completely explicit:
--
--   for every anchored polynomial SAT candidate, construct an observer
--   factorization AND derive a SAT/UNSAT collision in its representation.
--
-- Merely constructing a polynomial observer is insufficient.  In particular,
-- PNotEqualsNPPolynomialObserverNoGoExact proves polynomial-time and reversible
-- encodings can be injective.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Mathematics.Complexity.CookLevinCircuitGCTBoundary as Cook
import DASHI.Mathematics.Complexity.PolynomialClassicalObserverExact as PolyObserver
import DASHI.Mathematics.Complexity.PolynomialReductionExact as PR
import DASHI.Mathematics.Complexity.PNotEqualsNPDirectSATLowerBoundExact as Direct
import DASHI.Mathematics.Complexity.PNotEqualsNPClayCoreExact as Clay
import DASHI.Mathematics.Complexity.PNotEqualsNPPolynomialObserverNoGoExact as NoGo

------------------------------------------------------------------------
-- A SAT-relevant collision is a property of the representation, not merely of
-- the downstream decision bit.
------------------------------------------------------------------------

record SATRelevantRepresentationCollision
    {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {anchored : Direct.AnchoredPolynomialSATDeciderCandidate cost}
    (observer :
      PolyObserver.PolynomialClassicalObserver
        cost
        (Direct.decide (Direct.candidate anchored))) : Set₁ where
  constructor sat-relevant-representation-collision
  field
    satisfiableFormula : Cook.BooleanFormula
    unsatisfiableFormula : Cook.BooleanFormula
    satisfiableWitness :
      Cook.Satisfiable satisfiableFormula
    unsatisfiableWitness :
      Cook.Satisfiable unsatisfiableFormula → ⊥
    sameRepresentation :
      PolyObserver.representation observer satisfiableFormula
      ≡
      PolyObserver.representation observer unsatisfiableFormula

open SATRelevantRepresentationCollision public

------------------------------------------------------------------------
-- Existing observer factorization now genuinely feeds the Clay path.
------------------------------------------------------------------------

observerCollisionGivesDirectSATCollision :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {anchored : Direct.AnchoredPolynomialSATDeciderCandidate cost}
    (observer :
      PolyObserver.PolynomialClassicalObserver
        cost
        (Direct.decide (Direct.candidate anchored))) →
  SATRelevantRepresentationCollision observer →
  Direct.SATDecisionCollision anchored
observerCollisionGivesDirectSATCollision
    {anchored = anchored}
    observer collision =
  Direct.sat-decision-collision
    (satisfiableFormula collision)
    (unsatisfiableFormula collision)
    (satisfiableWitness collision)
    (unsatisfiableWitness collision)
    decisionSame
  where
    decisionSame :
      Direct.decide (Direct.candidate anchored)
        (satisfiableFormula collision)
      ≡
      Direct.decide (Direct.candidate anchored)
        (unsatisfiableFormula collision)
    decisionSame =
      trans
        (PolyObserver.consumerFactors observer
          (satisfiableFormula collision))
        (trans
          (cong
            (PolyObserver.recoverDecision observer)
            (sameRepresentation collision))
          (sym
            (PolyObserver.consumerFactors observer
              (unsatisfiableFormula collision))))

observerCollisionGivesDecisionFailure :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {anchored : Direct.AnchoredPolynomialSATDeciderCandidate cost}
    (observer :
      PolyObserver.PolynomialClassicalObserver
        cost
        (Direct.decide (Direct.candidate anchored))) →
  SATRelevantRepresentationCollision observer →
  Direct.SATDecisionFailure (Direct.candidate anchored)
observerCollisionGivesDecisionFailure observer collision =
  Direct.collisionGivesDecisionFailure
    (observerCollisionGivesDirectSATCollision observer collision)

------------------------------------------------------------------------
-- The representation collision must be genuinely lossy.
------------------------------------------------------------------------

satRelevantCollisionForcesRepresentationNonInjective :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {anchored : Direct.AnchoredPolynomialSATDeciderCandidate cost}
    {observer :
      PolyObserver.PolynomialClassicalObserver
        cost
        (Direct.decide (Direct.candidate anchored))} →
  SATRelevantRepresentationCollision observer →
  NoGo.Injective (PolyObserver.representation observer) →
  ⊥
satRelevantCollisionForcesRepresentationNonInjective collision injective =
  NoGo.injectiveFormulaObserverCannotCollapseSATAndUNSAT
    injective
    (satisfiableFormula collision)
    (unsatisfiableFormula collision)
    (satisfiableWitness collision)
    (unsatisfiableWitness collision)
    (sameRepresentation collision)


------------------------------------------------------------------------
-- Structural-mechanism compiler.
--
-- A proposed lower-bound mechanism may choose its observer as a function of
-- the candidate.  To count as progress it must then DERIVE the SAT-relevant
-- collision for that chosen observer.  The compiler below is intentionally
-- neutral about how the observer is chosen; no collision field is hidden in a
-- generic status record.
------------------------------------------------------------------------

observerMechanismGivesAnchoredCollision :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    (observerFor :
      (anchored : Direct.AnchoredPolynomialSATDeciderCandidate cost) →
      PolyObserver.PolynomialClassicalObserver
        cost
        (Direct.decide (Direct.candidate anchored))) →
    ((anchored : Direct.AnchoredPolynomialSATDeciderCandidate cost) →
      SATRelevantRepresentationCollision (observerFor anchored)) →
  Direct.UniversalAnchoredPolynomialSATDecisionCollision cost
observerMechanismGivesAnchoredCollision observerFor collisionFor anchored =
  observerCollisionGivesDirectSATCollision
    (observerFor anchored)
    (collisionFor anchored)

observerMechanismGivesSATLowerBoundProducer :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    (observerFor :
      (anchored : Direct.AnchoredPolynomialSATDeciderCandidate cost) →
      PolyObserver.PolynomialClassicalObserver
        cost
        (Direct.decide (Direct.candidate anchored))) →
    ((anchored : Direct.AnchoredPolynomialSATDeciderCandidate cost) →
      SATRelevantRepresentationCollision (observerFor anchored)) →
  Clay.SATLowerBoundProducer cost
observerMechanismGivesSATLowerBoundProducer observerFor collisionFor =
  Direct.universalAnchoredCollisionGivesSATLowerBoundProducer
    (observerMechanismGivesAnchoredCollision observerFor collisionFor)
