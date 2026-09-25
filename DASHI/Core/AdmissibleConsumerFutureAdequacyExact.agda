module DASHI.Core.AdmissibleConsumerFutureAdequacyExact where

------------------------------------------------------------------------
-- ADMISSIBLE CONSUMER / FUTURE-OBSERVATIONAL ADEQUACY
--
-- This owner composes existing DASHI cores rather than defining another
-- factorisation or reachability theory.
--
-- Four obligations remain distinct:
--
--   1. query admissibility;
--   2. present consumer factorisation;
--   3. future-language safety over proof-bearing admissible traces;
--   4. resource/access realizability of the chosen projection and coarse
--      answer map.
--
-- In particular:
--
--   semantic adequacy != future safety != realizability.
--
-- A failed present factorisation is an exact fibre-collision witness.
-- A failed future safety obligation is a dynamic/terminalisation defect.
-- Future observations already range over AdmissibleReachability.Execut es,
-- so their endpoints lie in the proof-bearing admissible causal cone.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_)

import DASHI.Core.AdmissibleReachability as Reachability
import DASHI.Core.FutureObservationLanguageQuotientExact as FutureLanguage
import DASHI.Core.QueryIndexedProjectionAdequacyExact as Query
import DASHI.Core.TypedDependencyCore as Dependency

record AdmissibleConsumerProblem
    (State Action Observation QueryIndex Answer : Set) : Set₁ where
  constructor admissible-consumer-problem
  field
    system : Dependency.DependentActionSystem State Action
    project : State → Observation
    semantics : Query.QuerySemantics State QueryIndex Answer
    AdmissibleQuery : QueryIndex → Set

open AdmissibleConsumerProblem public

AdequateNow :
  ∀ {State Action Observation QueryIndex Answer} →
  AdmissibleConsumerProblem
    State Action Observation QueryIndex Answer →
  QueryIndex →
  Set₁
AdequateNow problem query =
  Query.AdequateFor
    (project problem)
    (semantics problem)
    query

AdmissibleAdequateNow :
  ∀ {State Action Observation QueryIndex Answer} →
  AdmissibleConsumerProblem
    State Action Observation QueryIndex Answer →
  QueryIndex →
  Set₁
AdmissibleAdequateNow problem query =
  AdmissibleQuery problem query
  ×
  AdequateNow problem query

record AdmissibleAdequacyDefect
    {State Action Observation QueryIndex Answer : Set}
    (problem :
      AdmissibleConsumerProblem
        State Action Observation QueryIndex Answer)
    (query : QueryIndex) : Set₁ where
  constructor admissible-adequacy-defect
  field
    queryIsAdmissible : AdmissibleQuery problem query
    factorisationDefect :
      Query.QueryAdequacyDefect
        (project problem)
        (semantics problem)
        query

open AdmissibleAdequacyDefect public

admissibilityDoesNotRepairNonFactorability :
  ∀ {State Action Observation QueryIndex Answer}
    {problem :
      AdmissibleConsumerProblem
        State Action Observation QueryIndex Answer}
    {query : QueryIndex} →
  AdmissibleAdequacyDefect problem query →
  AdmissibleAdequateNow problem query →
  ⊥
admissibilityDoesNotRepairNonFactorability
    defect
    (admissible , factorisation) =
  Query.queryAdequacyDefectBlocksFactorisation
    (factorisationDefect defect)
    factorisation

------------------------------------------------------------------------
-- Future-language safety for the same declared observation surface.
--
-- Equal current observations may be merged only when they have the same
-- complete action-indexed future observation language under admissible traces.
------------------------------------------------------------------------

FutureSafe :
  ∀ {State Action Observation QueryIndex Answer} →
  AdmissibleConsumerProblem
    State Action Observation QueryIndex Answer →
  Set₁
FutureSafe problem =
  FutureLanguage.FutureLanguageSafeProjection
    (system problem)
    (project problem)
    (project problem)

------------------------------------------------------------------------
-- Resource/access realizability.
--
-- The predicates are application supplied.  In a complexity application they
-- may mean polynomial-time computable; in an evidence application they may
-- mean obtainable from the authorised evidence surface.
------------------------------------------------------------------------

record OperationallyAdequate
    {State Action Observation QueryIndex Answer : Set}
    (ProjectRealizable : (State → Observation) → Set)
    (AnswerRealizable : (Observation → Answer) → Set)
    (problem :
      AdmissibleConsumerProblem
        State Action Observation QueryIndex Answer)
    (query : QueryIndex) : Set₁ where
  constructor operationally-adequate
  field
    operationalQueryAdmissible :
      AdmissibleQuery problem query
    projectionRealizable :
      ProjectRealizable (project problem)
    coarseAnswer :
      Observation → Answer
    coarseAnswerRealizable :
      AnswerRealizable coarseAnswer
    operationalFactorisation :
      (state : State) →
      Query.answer (semantics problem) query state
      ≡
      coarseAnswer (project problem state)

open OperationallyAdequate public

operationalAdequacyImpliesPresentAdequacy :
  ∀ {State Action Observation QueryIndex Answer}
    {ProjectRealizable : (State → Observation) → Set}
    {AnswerRealizable : (Observation → Answer) → Set}
    {problem :
      AdmissibleConsumerProblem
        State Action Observation QueryIndex Answer}
    {query : QueryIndex} →
  OperationallyAdequate
    ProjectRealizable AnswerRealizable problem query →
  AdmissibleAdequateNow problem query
operationalAdequacyImpliesPresentAdequacy operational =
  operationalQueryAdmissible operational
  ,
  Query.factorsForQuery
    (coarseAnswer operational)
    (operationalFactorisation operational)

record AdmissibleOperationalFutureAdequacy
    {State Action Observation QueryIndex Answer : Set}
    (ProjectRealizable : (State → Observation) → Set)
    (AnswerRealizable : (Observation → Answer) → Set)
    (problem :
      AdmissibleConsumerProblem
        State Action Observation QueryIndex Answer)
    (query : QueryIndex) : Set₁ where
  constructor admissible-operational-future-adequacy
  field
    operational :
      OperationallyAdequate
        ProjectRealizable AnswerRealizable problem query
    futureSafe :
      FutureSafe problem

open AdmissibleOperationalFutureAdequacy public

admissibleDefectBlocksOperationalAdequacy :
  ∀ {State Action Observation QueryIndex Answer}
    {ProjectRealizable : (State → Observation) → Set}
    {AnswerRealizable : (Observation → Answer) → Set}
    {problem :
      AdmissibleConsumerProblem
        State Action Observation QueryIndex Answer}
    {query : QueryIndex} →
  AdmissibleAdequacyDefect problem query →
  OperationallyAdequate
    ProjectRealizable AnswerRealizable problem query →
  ⊥
admissibleDefectBlocksOperationalAdequacy defect operational =
  admissibilityDoesNotRepairNonFactorability
    defect
    (operationalAdequacyImpliesPresentAdequacy operational)

------------------------------------------------------------------------
-- Future observations already live inside the admissible causal cone.
------------------------------------------------------------------------

record AdmissibleConeObservation
    {State Action Observation : Set}
    (system : Dependency.DependentActionSystem State Action)
    (project : State → Observation)
    (start : State)
    (observation : Observation) : Set where
  constructor admissible-cone-observation
  field
    endpoint : State
    endpointReachable :
      Reachability.Reachable system start endpoint
    endpointObservation :
      project endpoint ≡ observation

open AdmissibleConeObservation public

futureObservationLiesInAdmissibleCone :
  ∀ {State Action Observation}
    {system : Dependency.DependentActionSystem State Action}
    {project : State → Observation}
    {start : State}
    {actions : List Action}
    {observation : Observation} →
  FutureLanguage.FutureObservation
    system project start actions observation →
  AdmissibleConeObservation
    system project start observation
futureObservationLiesInAdmissibleCone
    (FutureLanguage.futureObservation after execution observed) =
  admissible-cone-observation
    after
    (Reachability.executesImpliesReachable execution)
    observed

------------------------------------------------------------------------
-- Non-promotions.
------------------------------------------------------------------------

data PresentAdequacyImpliesFutureSafetyPermission : Set where

presentAdequacyCannotManufactureFutureSafety :
  PresentAdequacyImpliesFutureSafetyPermission → ⊥
presentAdequacyCannotManufactureFutureSafety ()

data SemanticAdequacyImpliesRealizabilityPermission : Set where

semanticAdequacyCannotManufactureRealizability :
  SemanticAdequacyImpliesRealizabilityPermission → ⊥
semanticAdequacyCannotManufactureRealizability ()
