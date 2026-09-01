module DASHI.Core.ActionCrossingTraceCalculusExact where

------------------------------------------------------------------------
-- EXPLICIT ACTION-CROSSING TRACE CALCULUS
--
-- Persistent carriers are strands.  An action involving two carriers is an
-- ordered crossing event.  A trace is an ordered list of crossings.  Concatenating
-- traces is associative, while the order of crossing events remains provenance.
--
-- This is a structural action-history grammar only.  It does not assert that
-- every domain supplies a topological braid group or Yang-Baxter action.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Properties using (++-assoc)

record CrossingEvent (Strand Action : Set) : Set where
  constructor crossing-event
  field
    leftStrand : Strand
    rightStrand : Strand
    action : Action

open CrossingEvent public

ActionTrace : Set → Set → Set
ActionTrace Strand Action = List (CrossingEvent Strand Action)

emptyTrace : ∀ {Strand Action} → ActionTrace Strand Action
emptyTrace = []

singleCrossing :
  ∀ {Strand Action} →
  CrossingEvent Strand Action → ActionTrace Strand Action
singleCrossing event = event ∷ []

_++trace_ :
  ∀ {Strand Action} →
  ActionTrace Strand Action →
  ActionTrace Strand Action →
  ActionTrace Strand Action
_++trace_ = _++_

traceConcatenationAssociative :
  ∀ {Strand Action}
    (left middle right : ActionTrace Strand Action) →
  (left ++trace middle) ++trace right
  ≡ left ++trace (middle ++trace right)
traceConcatenationAssociative = ++-assoc

record TraceObservationSurface (Strand Action : Set) : Set₁ where
  constructor trace-observation-surface
  field
    Endpoint : Set
    Provenance : Set
    endpoint : ActionTrace Strand Action → Endpoint
    provenance : ActionTrace Strand Action → Provenance

open TraceObservationSurface public

record SameEndpointDifferentTraceProvenance
    {Strand Action : Set}
    (surface : TraceObservationSurface Strand Action) : Set where
  constructor same-endpoint-different-trace-provenance
  field
    leftTrace rightTrace : ActionTrace Strand Action
    sameEndpoint : endpoint surface leftTrace ≡ endpoint surface rightTrace
    differentProvenance :
      provenance surface leftTrace ≡ provenance surface rightTrace → ⊥

open SameEndpointDifferentTraceProvenance public

------------------------------------------------------------------------
-- No-promotion boundaries.
------------------------------------------------------------------------

data TraceConcatenationAssociativityErasesEventOrder : Set where

data EveryCrossingIsReversible : Set where

data EveryActionTraceFormsBraidGroupElement : Set where

data CrossingCountDeterminesProvenance : Set where

data MoreCrossingsMeanMoreObfuscation : Set where

associativityDoesNotEraseEventOrder :
  TraceConcatenationAssociativityErasesEventOrder → ⊥
associativityDoesNotEraseEventOrder ()

crossingsAreNotUniversallyReversible : EveryCrossingIsReversible → ⊥
crossingsAreNotUniversallyReversible ()

actionTracesAreNotPromotedToBraidGroupElements :
  EveryActionTraceFormsBraidGroupElement → ⊥
actionTracesAreNotPromotedToBraidGroupElements ()

crossingCountDoesNotDetermineProvenance : CrossingCountDeterminesProvenance → ⊥
crossingCountDoesNotDetermineProvenance ()

moreCrossingsDoNotUniversallyMeanMoreObfuscation : MoreCrossingsMeanMoreObfuscation → ⊥
moreCrossingsDoNotUniversallyMeanMoreObfuscation ()

record ActionCrossingTraceBoundary : Set where
  constructor action-crossing-trace-boundary
  field
    actionEventsAreExplicitCrossings : Bool
    crossingOrderIsFirstClass : Bool
    traceConcatenationAssociative : Bool
    associativityErasesOrder : Bool
    everyCrossingReversible : Bool
    braidGroupConstructed : Bool
    crossingCountDeterminesProvenance : Bool
    moreCrossingsAlwaysMeanMoreObfuscation : Bool

canonicalActionCrossingTraceBoundary : ActionCrossingTraceBoundary
canonicalActionCrossingTraceBoundary =
  action-crossing-trace-boundary true true true false false false false false
