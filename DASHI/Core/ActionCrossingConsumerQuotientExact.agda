module DASHI.Core.ActionCrossingConsumerQuotientExact where

------------------------------------------------------------------------
-- CONSUMER QUOTIENTS OVER ACTION-CROSSING TRACES
--
-- A declared consumer observes an ordered action trace through a projection.
-- Trace equivalence is therefore consumer-relative.  A rewrite/crossing change
-- may be invisible to one consumer and visible to another.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Core.ActionCrossingTraceCalculusExact as Trace

record TraceConsumer (Strand Action : Set) : Set₁ where
  constructor trace-consumer
  field
    Observation : Set
    observe : Trace.ActionTrace Strand Action → Observation

open TraceConsumer public

TraceEquivalent :
  ∀ {Strand Action} →
  TraceConsumer Strand Action →
  Trace.ActionTrace Strand Action →
  Trace.ActionTrace Strand Action → Set
TraceEquivalent consumer left right =
  observe consumer left ≡ observe consumer right

record TraceRewrite {Strand Action : Set} : Set where
  constructor trace-rewrite
  field
    before after : Trace.ActionTrace Strand Action

open TraceRewrite public

record InvisibleTo
    {Strand Action : Set}
    (consumer : TraceConsumer Strand Action)
    (rewrite : TraceRewrite {Strand} {Action}) : Set where
  constructor invisible-to
  field
    observationPreserved :
      TraceEquivalent consumer (before rewrite) (after rewrite)

open InvisibleTo public

record VisibleTo
    {Strand Action : Set}
    (consumer : TraceConsumer Strand Action)
    (rewrite : TraceRewrite {Strand} {Action}) : Set where
  constructor visible-to
  field
    observationChanges :
      TraceEquivalent consumer (before rewrite) (after rewrite) → ⊥

open VisibleTo public

record ConsumerSplit
    {Strand Action : Set}
    (coarse fine : TraceConsumer Strand Action)
    (rewrite : TraceRewrite {Strand} {Action}) : Set where
  constructor consumer-split
  field
    coarseInvisible : InvisibleTo coarse rewrite
    fineVisible : VisibleTo fine rewrite

open ConsumerSplit public

------------------------------------------------------------------------
-- Residual for later reopening: the coarse quotient may collapse a rewrite,
-- while a retained residual records which fine representative was carried.
------------------------------------------------------------------------

data RepresentativeSide : Set where
  beforeRepresentative afterRepresentative : RepresentativeSide

record ReopenableConsumerCollapse
    {Strand Action : Set}
    (coarse : TraceConsumer Strand Action)
    (rewrite : TraceRewrite {Strand} {Action}) : Set where
  constructor reopenable-consumer-collapse
  field
    collapsedForCoarseConsumer : InvisibleTo coarse rewrite
    residual : RepresentativeSide

open ReopenableConsumerCollapse public

------------------------------------------------------------------------
-- Boundaries.
------------------------------------------------------------------------

data InvisibleToOneMeansInvisibleToAll : Set where

data ConsumerEquivalenceIsTraceIdentity : Set where

data CoarseCollapseErasesActualHistory : Set where

data ResidualMeansWrongdoing : Set where

data ConsumerObservationCreatesAuthority : Set where

invisibilityIsNotUniversalAcrossConsumers : InvisibleToOneMeansInvisibleToAll → ⊥
invisibilityIsNotUniversalAcrossConsumers ()

consumerEquivalenceIsNotTraceIdentity : ConsumerEquivalenceIsTraceIdentity → ⊥
consumerEquivalenceIsNotTraceIdentity ()

coarseCollapseDoesNotEraseActualHistory : CoarseCollapseErasesActualHistory → ⊥
coarseCollapseDoesNotEraseActualHistory ()

residualDoesNotMeanWrongdoing : ResidualMeansWrongdoing → ⊥
residualDoesNotMeanWrongdoing ()

consumerObservationDoesNotCreateAuthority : ConsumerObservationCreatesAuthority → ⊥
consumerObservationDoesNotCreateAuthority ()

record ActionCrossingConsumerQuotientBoundary : Set where
  constructor action-crossing-consumer-quotient-boundary
  field
    traceEquivalenceConsumerRelative : Bool
    rewriteCanBeInvisibleToOneConsumer : Bool
    sameRewriteCanBeVisibleToAnother : Bool
    residualSupportsLaterReopening : Bool
    consumerEquivalenceMeansTraceIdentity : Bool
    coarseCollapseErasesHistory : Bool
    residualImpliesWrongdoing : Bool

canonicalActionCrossingConsumerQuotientBoundary :
  ActionCrossingConsumerQuotientBoundary
canonicalActionCrossingConsumerQuotientBoundary =
  action-crossing-consumer-quotient-boundary true true true true false false false
