module DASHI.Mathematics.Complexity.PNotEqualsNPCandidateFirstStepProgressStrengthExact where

------------------------------------------------------------------------
-- FIRST-STEP PROGRESS STRENGTH AUDIT
--
-- The current CandidateFirstStepProgress predicate is intentionally operational:
--
--   constructor (initialFor candidate) != nothing.
--
-- Before using it as a lower-bound premise, audit whether its universal form
-- already contains candidate semantics.
--
-- Result: it does not.  In fact the current type permits the initial-state
-- builder to ignore the candidate entirely.  A single unrelated progressing
-- state can therefore be lifted to "progress for every polynomial candidate".
--
-- This is stronger than a prose warning: the candidate quantifier is formally
-- erasable for constant builders.
--
-- Consequence:
--   universal first-step progress on the current loose interface must NOT be
--   interpreted as SAT-failure strength.  It is too weakly coupled to D.
--
-- The next admissible progress theorem must quantify over an actual
-- candidate/self-code realization, not merely CandidateInitialRootBuilder.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (_≢_)
open import Data.Empty using (⊥)
open import Data.Maybe.Base using (nothing)

import DASHI.Mathematics.Complexity.CookLevinCircuitGCTBoundary as Cook
import DASHI.Mathematics.Complexity.PolynomialReductionExact as PR
import DASHI.Mathematics.Complexity.PNotEqualsNPDirectSATLowerBoundExact as Direct
import DASHI.Mathematics.Complexity.PNotEqualsNPBoundedSelfReferenceWellFoundedExact as Q2
import DASHI.Mathematics.Complexity.PNotEqualsNPDirectDPChargedRecurrenceExact as DirectDP
import DASHI.Mathematics.Complexity.PNotEqualsNPCandidateCoupledFirstStepBoundaryExact as Boundary

------------------------------------------------------------------------
-- Universal progress surface.
------------------------------------------------------------------------

UniversalCandidateFirstStepProgress :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula} →
  Boundary.CandidateInitialRootBuilder cost →
  DirectDP.DirectDPChargedStateConstructor →
  Set₁
UniversalCandidateFirstStepProgress
    {cost}
    initialFor
    constructor =
  (candidate : Direct.PolynomialSATDeciderCandidate cost) →
  Boundary.CandidateFirstStepProgress
    initialFor
    constructor
    candidate

------------------------------------------------------------------------
-- Candidate-erasing root builder.
------------------------------------------------------------------------

constantInitialRootBuilder :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula} →
  Q2.BoundedSelfReferenceState →
  Boundary.CandidateInitialRootBuilder cost
constantInitialRootBuilder state candidate =
  state

constantBuilderProgressIgnoresCandidate :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {state : Q2.BoundedSelfReferenceState}
    {constructor : DirectDP.DirectDPChargedStateConstructor} →
  constructor state ≢ nothing →
  UniversalCandidateFirstStepProgress
    (constantInitialRootBuilder {cost} state)
    constructor
constantBuilderProgressIgnoresCandidate
    progresses
    candidate =
  progresses

------------------------------------------------------------------------
-- Conversely, universal progress for a constant builder contains no more than
-- progress at the single fixed state.  We need one candidate only to project
-- the universal statement.
------------------------------------------------------------------------

constantBuilderUniversalProgressProjects :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {state : Q2.BoundedSelfReferenceState}
    {constructor : DirectDP.DirectDPChargedStateConstructor}
    (candidate : Direct.PolynomialSATDeciderCandidate cost) →
  UniversalCandidateFirstStepProgress
    (constantInitialRootBuilder {cost} state)
    constructor →
  constructor state ≢ nothing
constantBuilderUniversalProgressProjects
    candidate
    universal =
  universal candidate

record ConstantBuilderProgressEquivalence
    {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    (state : Q2.BoundedSelfReferenceState)
    (constructor : DirectDP.DirectDPChargedStateConstructor)
    (candidate : Direct.PolynomialSATDeciderCandidate cost) : Set₁ where
  constructor constant-builder-progress-equivalence
  field
    oneStateToUniversal :
      constructor state ≢ nothing →
      UniversalCandidateFirstStepProgress
        (constantInitialRootBuilder {cost} state)
        constructor

    universalToOneState :
      UniversalCandidateFirstStepProgress
        (constantInitialRootBuilder {cost} state)
        constructor →
      constructor state ≢ nothing

open ConstantBuilderProgressEquivalence public

constantBuilderProgressEquivalence :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    (state : Q2.BoundedSelfReferenceState)
    (constructor : DirectDP.DirectDPChargedStateConstructor)
    (candidate : Direct.PolynomialSATDeciderCandidate cost) →
  ConstantBuilderProgressEquivalence
    state
    constructor
    candidate
constantBuilderProgressEquivalence
    state
    constructor
    candidate =
  constant-builder-progress-equivalence
    constantBuilderProgressIgnoresCandidate
    (constantBuilderUniversalProgressProjects candidate)

------------------------------------------------------------------------
-- Extensional transport: progress only observes the selected state.
-- It does not inspect the candidate's decision function directly.
------------------------------------------------------------------------

progressTransportAcrossSameSelectedState :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {initialFor : Boundary.CandidateInitialRootBuilder cost}
    {constructor : DirectDP.DirectDPChargedStateConstructor}
    {left right : Direct.PolynomialSATDeciderCandidate cost} →
  initialFor left ≡ initialFor right →
  Boundary.CandidateFirstStepProgress
    initialFor
    constructor
    left →
  Boundary.CandidateFirstStepProgress
    initialFor
    constructor
    right
progressTransportAcrossSameSelectedState
    refl
    progress =
  progress

------------------------------------------------------------------------
-- Strength verdict.
--
-- We do NOT assert a metatheoretic non-implication
--
--   UniversalProgress ->/ SATDecisionFailure,
--
-- inside Agda: proving that would itself require an explicit model/candidate
-- with no SAT error, i.e. essentially the unresolved complexity question.
--
-- What is proved internally is the relevant architectural fact:
--
--   the current universal-progress quantifier can be satisfied by a builder
--   that erases D completely.
--
-- Therefore any future implication from this loose progress surface to a SAT
-- failure would have to use extra hypotheses not present in progress itself.
-- The route survives the circularity audit only after replacing the loose
-- builder with a same-object candidate/self-code realization.
------------------------------------------------------------------------

data FirstStepProgressStrengthStatus : Set where
  candidateQuantifierCanBeErasedByConstantBuilder : FirstStepProgressStrengthStatus
  directCandidateDecisionSemanticsPresent : FirstStepProgressStrengthStatus
  sameObjectSelfInstantiationCouplingPresent : FirstStepProgressStrengthStatus

currentFirstStepProgressStatus :
  FirstStepProgressStrengthStatus
currentFirstStepProgressStatus =
  candidateQuantifierCanBeErasedByConstantBuilder

data LooseProgressAlreadyCountsAsSATFailure : Set where

looseProgressNotPromotedToSATFailure :
  LooseProgressAlreadyCountsAsSATFailure → ⊥
looseProgressNotPromotedToSATFailure ()
