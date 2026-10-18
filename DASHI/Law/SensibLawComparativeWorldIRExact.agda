module DASHI.Law.SensibLawComparativeWorldIRExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.IntersectionalNonFactorability as NF
import DASHI.Core.QueryIndexedProjectionAdequacyExact as Query

------------------------------------------------------------------------
-- M11 / S26 COMPARATIVE WORLD IR
--
-- Comparison is query-indexed.  A world delta is not an answer delta merely
-- because the worlds differ.  The query-relevant projection must carry enough
-- information for the queried answer to factor through it.
------------------------------------------------------------------------

data DeltaKind : Set where
  factAdded factRemoved factChanged : DeltaKind
  reviewStateChanged scopeChanged authorityChanged applicabilityChanged : DeltaKind
  defeaterAdded defeaterRemoved counterDefeaterAdded counterDefeaterRemoved : DeltaKind
  jurisdictionChanged asAtChanged consumerDependencyChanged : DeltaKind
  residualOpened residualClosed routeStatusChanged : DeltaKind

data DeltaRole : Set where
  worldInput proofOutcome residualOutcome contextDelta : DeltaRole

record ComparativeDelta : Set where
  constructor comparative-delta
  field
    deltaRef : String
    kind : DeltaKind
    role : DeltaRole
    coordinateRef : String
    routeRef : String
    candidateOnly : Bool
    createsSemanticAuthority : Bool
    createsClaimTruth : Bool

open ComparativeDelta public

record ComparativeWorldIR : Set where
  constructor comparative-world-ir
  field
    leftWorldRef : String
    rightWorldRef : String
    sharedCoordinateRefs : List String
    changedCoordinateRefs : List String
    sharedRouteRefs : List String
    changedRouteRefs : List String
    changedResidualRefs : List String
    queryRelevantChanges : List ComparativeDelta
    queryIrrelevantChanges : List ComparativeDelta
    candidateOnly : Bool
    createsSemanticAuthority : Bool
    createsClaimTruth : Bool

open ComparativeWorldIR public

------------------------------------------------------------------------
-- Query-indexed adequacy reuses the repository-wide FactorsThrough owner.
------------------------------------------------------------------------

data DemoWorld : Set where
  sameAnswerNoiseLeft : DemoWorld
  sameAnswerNoiseRight : DemoWorld
  answerChangingLeft : DemoWorld
  answerChangingRight : DemoWorld

data DemoQuery : Set where
  dutyRouteQuery : DemoQuery

data QuerySurface : Set where
  routeOpenSurface : QuerySurface
  routeDefeatedSurface : QuerySurface

data DemoAnswer : Set where
  reachableAnswer : DemoAnswer
  defeatedAnswer : DemoAnswer

queryProjection : DemoWorld → QuerySurface
queryProjection sameAnswerNoiseLeft = routeOpenSurface
queryProjection sameAnswerNoiseRight = routeOpenSurface
queryProjection answerChangingLeft = routeOpenSurface
queryProjection answerChangingRight = routeDefeatedSurface

demoAnswer : DemoQuery → DemoWorld → DemoAnswer
demoAnswer dutyRouteQuery sameAnswerNoiseLeft = reachableAnswer
demoAnswer dutyRouteQuery sameAnswerNoiseRight = reachableAnswer
demoAnswer dutyRouteQuery answerChangingLeft = reachableAnswer
demoAnswer dutyRouteQuery answerChangingRight = defeatedAnswer

demoSemantics : Query.QuerySemantics DemoWorld DemoQuery DemoAnswer
demoSemantics = Query.querySemantics demoAnswer

answerFromSurface : QuerySurface → DemoAnswer
answerFromSurface routeOpenSurface = reachableAnswer
answerFromSurface routeDefeatedSurface = defeatedAnswer

queryRelevantProjectionAdequate :
  Query.AdequateFor queryProjection demoSemantics dutyRouteQuery
queryRelevantProjectionAdequate =
  Query.factorsForQuery
    {project = queryProjection}
    {semantics = demoSemantics}
    {query = dutyRouteQuery}
    answerFromSurface
    (λ
      { sameAnswerNoiseLeft → refl
      ; sameAnswerNoiseRight → refl
      ; answerChangingLeft → refl
      ; answerChangingRight → refl
      })

worldsMayDifferWithoutAnswerDifference :
  demoAnswer dutyRouteQuery sameAnswerNoiseLeft
    ≡ demoAnswer dutyRouteQuery sameAnswerNoiseRight
worldsMayDifferWithoutAnswerDifference = refl

------------------------------------------------------------------------
-- Dropping the answer-changing axis is not adequate.
------------------------------------------------------------------------

data FlatWorldDifference : Set where
  someWorldDifference : FlatWorldDifference

flatDifferenceOnly : DemoWorld → FlatWorldDifference
flatDifferenceOnly world = someWorldDifference

answerChangingProjectionDefect :
  Query.QueryAdequacyDefect
    flatDifferenceOnly
    demoSemantics
    dutyRouteQuery
answerChangingProjectionDefect =
  Query.queryAdequacyDefect
    {project = flatDifferenceOnly}
    {semantics = demoSemantics}
    {query = dutyRouteQuery}
    answerChangingLeft
    answerChangingRight
    refl
    (λ ())

flatWorldDifferenceDoesNotDetermineAnswer :
  Query.AdequateFor flatDifferenceOnly demoSemantics dutyRouteQuery → ⊥
flatWorldDifferenceDoesNotDetermineAnswer =
  Query.queryAdequacyDefectBlocksFactorisation
    {project = flatDifferenceOnly}
    {semantics = demoSemantics}
    {query = dutyRouteQuery}
    answerChangingProjectionDefect

------------------------------------------------------------------------
-- Input/outcome separation.
------------------------------------------------------------------------

isCandidateCause : DeltaRole → Bool
isCandidateCause worldInput = true
isCandidateCause contextDelta = true
isCandidateCause proofOutcome = false
isCandidateCause residualOutcome = false

proofOutcomeCannotBeItsOwnCause :
  isCandidateCause proofOutcome ≡ false
proofOutcomeCannotBeItsOwnCause = refl

residualOutcomeCannotBeItsOwnCause :
  isCandidateCause residualOutcome ≡ false
residualOutcomeCannotBeItsOwnCause = refl

data WorldDifferenceAutomaticallyChangesAnswer : Set where
data ProofOutcomeMayServeAsAnswerChangingCause : Set where
data QueryIrrelevantDeltaMayForceRecompute : Set where
data ComparisonCreatesSemanticAuthority : Set where
data ComparisonCreatesClaimTruth : Set where

worldDifferenceDoesNotAutoChangeAnswer :
  WorldDifferenceAutomaticallyChangesAnswer → ⊥
worldDifferenceDoesNotAutoChangeAnswer ()

proofOutcomeCannotServeAsItsOwnCause :
  ProofOutcomeMayServeAsAnswerChangingCause → ⊥
proofOutcomeCannotServeAsItsOwnCause ()

queryIrrelevantDeltaCannotForceRecompute :
  QueryIrrelevantDeltaMayForceRecompute → ⊥
queryIrrelevantDeltaCannotForceRecompute ()

comparisonDoesNotCreateAuthority :
  ComparisonCreatesSemanticAuthority → ⊥
comparisonDoesNotCreateAuthority ()

comparisonDoesNotCreateTruth :
  ComparisonCreatesClaimTruth → ⊥
comparisonDoesNotCreateTruth ()

record ComparativeWorldBoundary : Set where
  constructor comparativeWorldBoundary
  field
    worldsMayDifferWithoutAnswerDiffering : Bool
    worldsMayDifferWithoutAnswerDifferingIsTrue :
      worldsMayDifferWithoutAnswerDiffering ≡ true

    queryIndexRequired : Bool
    queryIndexRequiredIsTrue :
      queryIndexRequired ≡ true

    answerChangingCauseMustBeInputSide : Bool
    answerChangingCauseMustBeInputSideIsTrue :
      answerChangingCauseMustBeInputSide ≡ true

    proofOutcomeIsNotOwnCause : Bool
    proofOutcomeIsNotOwnCauseIsTrue :
      proofOutcomeIsNotOwnCause ≡ true

    comparisonCreatesAuthority : Bool
    comparisonCreatesAuthorityIsFalse :
      comparisonCreatesAuthority ≡ false

    comparisonCreatesTruth : Bool
    comparisonCreatesTruthIsFalse :
      comparisonCreatesTruth ≡ false

open ComparativeWorldBoundary public

canonicalComparativeWorldBoundary : ComparativeWorldBoundary
canonicalComparativeWorldBoundary =
  comparativeWorldBoundary
    true refl
    true refl
    true refl
    true refl
    false refl
    false refl
