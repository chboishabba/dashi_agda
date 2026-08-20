module DASHI.Core.QueryIndexedProjectionAdequacyExact where

------------------------------------------------------------------------
-- QUERY-INDEXED PROJECTION ADEQUACY
--
-- A projection is not intrinsically "adequate".  Adequacy is indexed by the
-- query / intervention language being asked of it.  For a fixed query, the fine
-- answer must factor through the projection.  An exact fibre collision with
-- different fine answers therefore refutes adequacy for that query.
--
-- This module deliberately reuses IntersectionalNonFactorability.FactorsThrough
-- and NonFactorabilityWitness rather than defining a parallel factorisation
-- calculus.
--
-- Conceptual precedent:
-- David Blackwell, "Equivalent Comparisons of Experiments",
-- Annals of Mathematical Statistics 24(2), 265-272 (1953).
-- DOI: 10.1214/aoms/1177729032.
--
-- Blackwell is cited only as precedent for comparing information carried by
-- observations/experiments.  Query-indexing of the existing DASHI
-- factorisation carrier is a repository-local construction.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Core.IntersectionalNonFactorability as NonFactor

record QuerySemantics (State Query Answer : Set) : Set₁ where
  constructor querySemantics
  field
    answer : Query → State → Answer

open QuerySemantics public

AdequateFor :
  ∀ {State Observation Query Answer} →
  (State → Observation) →
  QuerySemantics State Query Answer →
  Query → Set₁
AdequateFor project semantics query =
  NonFactor.FactorsThrough project (answer semantics query)

QueryAdequacyDefect :
  ∀ {State Observation Query Answer} →
  (State → Observation) →
  QuerySemantics State Query Answer →
  Query → Set₁
QueryAdequacyDefect project semantics query =
  NonFactor.NonFactorabilityWitness project (answer semantics query)

-- Compatibility constructors keep the query-indexed call sites readable while
-- delegating the actual carrier to IntersectionalNonFactorability.
factorsForQuery :
  ∀ {State Observation Query Answer}
    {project : State → Observation}
    {semantics : QuerySemantics State Query Answer}
    {query : Query} →
  (coarseAnswer : Observation → Answer) →
  ((state : State) →
    answer semantics query state ≡ coarseAnswer (project state)) →
  AdequateFor project semantics query
factorsForQuery coarseAnswer factorisation =
  NonFactor.factorsThrough coarseAnswer factorisation

queryAdequacyDefect :
  ∀ {State Observation Query Answer}
    {project : State → Observation}
    {semantics : QuerySemantics State Query Answer}
    {query : Query} →
  (left right : State) →
  project left ≡ project right →
  (answer semantics query left ≡ answer semantics query right → ⊥) →
  QueryAdequacyDefect project semantics query
queryAdequacyDefect left right same different =
  NonFactor.nonFactorabilityWitness left right same different

queryAdequacyDefectBlocksFactorisation :
  ∀ {State Observation Query Answer}
    {project : State → Observation}
    {semantics : QuerySemantics State Query Answer}
    {query : Query} →
  QueryAdequacyDefect project semantics query →
  AdequateFor project semantics query →
  ⊥
queryAdequacyDefectBlocksFactorisation =
  NonFactor.witnessRulesOutEveryFlatFactorisation

------------------------------------------------------------------------
-- Exact witness: the same projection is adequate for one query and inadequate
-- for another.  This rules out an intrinsic Boolean notion of projection
-- adequacy even in a two-state finite model.
------------------------------------------------------------------------

data DemoState : Set where leftState rightState : DemoState
data DemoObservation : Set where sameSurface : DemoObservation
data DemoQuery : Set where surfaceQuery distinguishingQuery : DemoQuery
data DemoAnswer : Set where surfaceAnswer leftAnswer rightAnswer : DemoAnswer

demoProject : DemoState → DemoObservation
demoProject state = sameSurface

demoAnswer : DemoQuery → DemoState → DemoAnswer
demoAnswer surfaceQuery state = surfaceAnswer
demoAnswer distinguishingQuery leftState = leftAnswer
demoAnswer distinguishingQuery rightState = rightAnswer

demoSemantics : QuerySemantics DemoState DemoQuery DemoAnswer
demoSemantics = querySemantics demoAnswer

surfaceQueryAdequate : AdequateFor demoProject demoSemantics surfaceQuery
surfaceQueryAdequate =
  factorsForQuery (λ observation → surfaceAnswer) (λ state → refl)

distinguishingQueryDefect :
  QueryAdequacyDefect demoProject demoSemantics distinguishingQuery
distinguishingQueryDefect =
  queryAdequacyDefect
    leftState
    rightState
    refl
    (λ ())

distinguishingQueryNotAdequate :
  AdequateFor demoProject demoSemantics distinguishingQuery → ⊥
distinguishingQueryNotAdequate =
  queryAdequacyDefectBlocksFactorisation distinguishingQueryDefect

record SameProjectionDifferentQueryAdequacy : Set₁ where
  constructor sameProjectionDifferentQueryAdequacy
  field
    adequateQuery : AdequateFor demoProject demoSemantics surfaceQuery
    inadequateQueryDefect :
      QueryAdequacyDefect demoProject demoSemantics distinguishingQuery

sameProjectionCanBeAdequateForOneQueryAndUnsafeForAnother :
  SameProjectionDifferentQueryAdequacy
sameProjectionCanBeAdequateForOneQueryAndUnsafeForAnother =
  sameProjectionDifferentQueryAdequacy
    surfaceQueryAdequate
    distinguishingQueryDefect

record QueryIndexedProjectionAdequacyBoundary : Set where
  constructor queryIndexedProjectionAdequacyBoundary
  field
    projectionAdequacyIsIntrinsicBoolean : Bool
    adequacyRequiresQueryIndex : Bool
    oneQueryAdequacyImpliesAllQueryAdequacy : Bool
    fibreCollisionCanRefuteQueryAdequacy : Bool

canonicalQueryIndexedProjectionAdequacyBoundary :
  QueryIndexedProjectionAdequacyBoundary
canonicalQueryIndexedProjectionAdequacyBoundary =
  queryIndexedProjectionAdequacyBoundary false true false true
