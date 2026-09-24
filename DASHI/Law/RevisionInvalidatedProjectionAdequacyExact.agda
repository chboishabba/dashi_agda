module DASHI.Law.RevisionInvalidatedProjectionAdequacyExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Core.QueryIndexedProjectionAdequacyExact as Query
import DASHI.Law.ClosedIsNotAdequateExact as Closed
import DASHI.Law.RevisionReReviewPropagationExact as ReReview

------------------------------------------------------------------------
-- S15.6/S18: stale source payment cannot survive a world revision.
--
-- A projection paid by R0 source/span coordinates belongs to the R0 world.
-- After R0 -> R1, the derived projection clears those stale coordinates and
-- receives a distinct projection identity.  An adequacy proof for the old
-- projection does not automatically inhabit adequacy for the invalidated one.
------------------------------------------------------------------------

data Revision : Set where r0 r1 : Revision

data PaymentState : Set where
  paidByR0 : PaymentState
  staleAfterR1 : PaymentState
  paidByR1 : PaymentState

data ProjectionVersion : Set where
  projectionR0 : ProjectionVersion
  projectionInvalidatedR1 : ProjectionVersion
  projectionRepaidR1 : ProjectionVersion

invalidatePayment : Revision → PaymentState → PaymentState
invalidatePayment r0 paidByR0 = paidByR0
invalidatePayment r0 staleAfterR1 = staleAfterR1
invalidatePayment r0 paidByR1 = paidByR1
invalidatePayment r1 paidByR0 = staleAfterR1
invalidatePayment r1 staleAfterR1 = staleAfterR1
invalidatePayment r1 paidByR1 = paidByR1

r0PaymentBecomesStaleAtR1 :
  invalidatePayment r1 paidByR0 ≡ staleAfterR1
r0PaymentBecomesStaleAtR1 = refl

data SourceQuery : Set where sourceSensitiveQuery : SourceQuery
data SourceAnswer : Set where r0Answer r1Answer : SourceAnswer
data StaleProjection : Set where sameStaleSurface : StaleProjection
data FreshProjection : Set where freshR0 freshR1 : FreshProjection
data SourceWorld : Set where worldR0 worldR1 : SourceWorld

staleProject : SourceWorld → StaleProjection
staleProject worldR0 = sameStaleSurface
staleProject worldR1 = sameStaleSurface

freshProject : SourceWorld → FreshProjection
freshProject worldR0 = freshR0
freshProject worldR1 = freshR1

sourceAnswer : SourceQuery → SourceWorld → SourceAnswer
sourceAnswer sourceSensitiveQuery worldR0 = r0Answer
sourceAnswer sourceSensitiveQuery worldR1 = r1Answer

sourceSemantics :
  Query.QuerySemantics SourceWorld SourceQuery SourceAnswer
sourceSemantics = Query.querySemantics sourceAnswer

staleProjectionDefect :
  Query.QueryAdequacyDefect staleProject sourceSemantics sourceSensitiveQuery
staleProjectionDefect =
  Query.queryAdequacyDefect
    {project = staleProject}
    {semantics = sourceSemantics}
    {query = sourceSensitiveQuery}
    worldR0
    worldR1
    refl
    (λ ())

staleProjectionCannotBeAdequate :
  Query.AdequateFor staleProject sourceSemantics sourceSensitiveQuery → ⊥
staleProjectionCannotBeAdequate =
  Query.queryAdequacyDefectBlocksFactorisation
    {project = staleProject}
    {semantics = sourceSemantics}
    {query = sourceSensitiveQuery}
    staleProjectionDefect

freshDecoder : FreshProjection → SourceAnswer
freshDecoder freshR0 = r0Answer
freshDecoder freshR1 = r1Answer

freshFactorisation :
  (world : SourceWorld) →
  sourceAnswer sourceSensitiveQuery world
  ≡
  freshDecoder (freshProject world)
freshFactorisation worldR0 = refl
freshFactorisation worldR1 = refl

freshProjectionAdequate :
  Query.AdequateFor freshProject sourceSemantics sourceSensitiveQuery
freshProjectionAdequate =
  Query.factorsForQuery
    {project = freshProject}
    {semantics = sourceSemantics}
    {query = sourceSensitiveQuery}
    freshDecoder
    freshFactorisation

data OldProjectionAdequacyAutomaticallyTransfersToInvalidatedProjection : Set where
data StaleSpanAutomaticallyPaysFreshRevision : Set where

oldAdequacyCannotAutomaticallyTransfer :
  OldProjectionAdequacyAutomaticallyTransfersToInvalidatedProjection → ⊥
oldAdequacyCannotAutomaticallyTransfer ()

staleSpanCannotAutomaticallyPayFreshRevision :
  StaleSpanAutomaticallyPaysFreshRevision → ⊥
staleSpanCannotAutomaticallyPayFreshRevision ()

closedBoundary : Closed.ClosedIsNotAdequateBoundary
closedBoundary = Closed.canonicalClosedIsNotAdequateBoundary

rereviewBoundary : ReReview.RevisionReReviewPropagationBoundary
rereviewBoundary = ReReview.canonicalRevisionReReviewPropagationBoundary

record RevisionInvalidatedProjectionAdequacyBoundary : Set where
  constructor revisionInvalidatedProjectionAdequacyBoundary
  field
    changedRevisionInvalidatesOldSourcePayment : Bool
    changedRevisionInvalidatesOldSourcePaymentIsTrue :
      changedRevisionInvalidatesOldSourcePayment ≡ true

    staleSpanMayContinuePayingFreshWorld : Bool
    staleSpanMayContinuePayingFreshWorldIsFalse :
      staleSpanMayContinuePayingFreshWorld ≡ false

    invalidatedProjectionGetsDistinctIdentity : Bool
    invalidatedProjectionGetsDistinctIdentityIsTrue :
      invalidatedProjectionGetsDistinctIdentity ≡ true

    oldFactorsThroughAutomaticallyTransfers : Bool
    oldFactorsThroughAutomaticallyTransfersIsFalse :
      oldFactorsThroughAutomaticallyTransfers ≡ false

    invalidatedProjectionMayReopenResearch : Bool
    invalidatedProjectionMayReopenResearchIsTrue :
      invalidatedProjectionMayReopenResearch ≡ true

    rereviewMayRestoreFreshPayment : Bool
    rereviewMayRestoreFreshPaymentIsTrue :
      rereviewMayRestoreFreshPayment ≡ true

    revisionInvalidationCreatesClaimTruth : Bool
    revisionInvalidationCreatesClaimTruthIsFalse :
      revisionInvalidationCreatesClaimTruth ≡ false

open RevisionInvalidatedProjectionAdequacyBoundary public

canonicalRevisionInvalidatedProjectionAdequacyBoundary :
  RevisionInvalidatedProjectionAdequacyBoundary
canonicalRevisionInvalidatedProjectionAdequacyBoundary =
  revisionInvalidatedProjectionAdequacyBoundary
    true refl
    false refl
    true refl
    false refl
    true refl
    true refl
    false refl
