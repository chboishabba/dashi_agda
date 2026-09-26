module DASHI.Mathematics.Complexity.PNotEqualsNPAdmissibleAdequacyCrossPollinationExact where

------------------------------------------------------------------------
-- P != NP / ADMISSIBLE CONSUMER ADEQUACY CROSS-POLLINATION
--
-- This owner does NOT prove a lower bound.
--
-- It instantiates the generic resource-realizability axis on the exact SAT
-- contradiction hypothesis already used by the Clay core:
--
--   satP : SAT in P.
--
-- Under satP, the decision bit itself is:
--
--   * an admissible present consumer projection;
--   * semantically exact for the SAT-decision consumer by definition; and
--   * polynomial-time realizable by the supplied PolynomialCostModel witness.
--
-- Therefore neither "there exists an adequate quotient" nor
-- "there exists a realizable adequate quotient" can be the lower-bound step.
-- The hard theorem must independently force a defect/non-realizability from
-- constraints that do not already inspect the SAT answer.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Unit using (⊤; tt)

import DASHI.Core.AdmissibleConsumerFutureAdequacyExact as Adequacy
import DASHI.Core.QueryIndexedProjectionAdequacyExact as Query
import DASHI.Core.ResourceIndexedObserverRefinementExact as Resource
import DASHI.Core.TypedDependencyCore as Dependency
import DASHI.Mathematics.Complexity.CookLevinCircuitGCTBoundary as Cook
import DASHI.Mathematics.Complexity.PNotEqualsNPClayCoreExact as Clay
import DASHI.Mathematics.Complexity.PolynomialReductionExact as PR

------------------------------------------------------------------------
-- Static SAT-decision problem as an admissible consumer problem.
--
-- No dynamic action is needed for this sanity theorem; the Shannon dynamic
-- lane remains owned by PNotEqualsNPSelfDiagonalFutureCongruenceExact.
------------------------------------------------------------------------

data SATDecisionQuery : Set where
  satDecisionQuery : SATDecisionQuery

data NoAction : Set where

noActionPrecondition :
  Cook.BooleanFormula → NoAction → Set
noActionPrecondition formula ()

noActionPostcondition :
  Cook.BooleanFormula → NoAction → Cook.BooleanFormula → Set
noActionPostcondition formula () after

noActionLabel : NoAction → String
noActionLabel ()

noActionSystem :
  Dependency.DependentActionSystem
    Cook.BooleanFormula
    NoAction
noActionSystem = record
  { Dependency.Precondition = noActionPrecondition
  ; Dependency.Postcondition = noActionPostcondition
  ; Dependency.actionLabel = noActionLabel
  }

satDecisionSemantics :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula} →
  PR.InP cost Clay.SATLanguage →
  Query.QuerySemantics
    Cook.BooleanFormula
    SATDecisionQuery
    Bool
satDecisionSemantics satP =
  Query.querySemantics answer
  where
    answer :
      SATDecisionQuery →
      Cook.BooleanFormula →
      Bool
    answer satDecisionQuery =
      PR.decide satP

satDecisionProblem :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula} →
  PR.InP cost Clay.SATLanguage →
  Adequacy.AdmissibleConsumerProblem
    Cook.BooleanFormula
    NoAction
    Bool
    SATDecisionQuery
    Bool
satDecisionProblem satP =
  Adequacy.admissible-consumer-problem
    noActionSystem
    (PR.decide satP)
    (satDecisionSemantics satP)
    (λ query → ⊤)

------------------------------------------------------------------------
-- Resource predicates.
------------------------------------------------------------------------

PolynomialProjectRealizable :
  (cost : PR.PolynomialCostModel Cook.BooleanFormula) →
  (Cook.BooleanFormula → Bool) →
  Set
PolynomialProjectRealizable cost =
  PR.polynomialTimeDecider cost

TrivialCoarseAnswerRealizable :
  (Bool → Bool) →
  Set
TrivialCoarseAnswerRealizable coarseAnswer =
  ⊤

------------------------------------------------------------------------
-- Under SAT in P, the circular truth projection is operationally adequate.
------------------------------------------------------------------------

satInPBuildsOperationallyAdequateTruthProjection :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    (satP : PR.InP cost Clay.SATLanguage) →
  Adequacy.OperationallyAdequate
    (PolynomialProjectRealizable cost)
    TrivialCoarseAnswerRealizable
    (satDecisionProblem satP)
    satDecisionQuery
satInPBuildsOperationallyAdequateTruthProjection satP =
  Adequacy.operationally-adequate
    tt
    (PR.polynomialDecision satP)
    identity
    tt
    (λ formula → refl)
  where
    identity : Bool → Bool
    identity bit = bit

satInPBuildsPresentAdequacy :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    (satP : PR.InP cost Clay.SATLanguage) →
  Adequacy.AdmissibleAdequateNow
    (satDecisionProblem satP)
    satDecisionQuery
satInPBuildsPresentAdequacy satP =
  Adequacy.operationalAdequacyImpliesPresentAdequacy
    (satInPBuildsOperationallyAdequateTruthProjection satP)

------------------------------------------------------------------------
-- Structural refinement does not pay the resource obligation.
--
-- This generic exact countermodel is intentionally independent of SAT.  It
-- records the logical shape needed by the P9 wall: proving that one observer
-- strictly refines another does not prove that the refined observer is
-- available inside the selected budget.
------------------------------------------------------------------------

structuralRefinementCanExceedBudget :
  Resource.RefinementBudgetFailure
    Resource.demoCoarse
    Resource.demoFine
structuralRefinementCanExceedBudget =
  Resource.canonicalRefinementBudgetFailure

------------------------------------------------------------------------
-- Explicit boundary receipt.
------------------------------------------------------------------------

record PNotEqualsNPAdequacyBoundary : Set where
  constructor p-not-equals-np-adequacy-boundary
  field
    semanticAdequacyAloneIsLowerBound : Bool
    realizableAdequacyUnderSatInPExists : Bool
    missingStepMustBeIndependentOfSATAnswer : Bool
    strictRefinementAlonePaysResourceBudget : Bool
    shannonDynamicOwnerRemainsSeparate : Bool

canonicalPNotEqualsNPAdequacyBoundary :
  PNotEqualsNPAdequacyBoundary
canonicalPNotEqualsNPAdequacyBoundary =
  p-not-equals-np-adequacy-boundary
    false true true false true
