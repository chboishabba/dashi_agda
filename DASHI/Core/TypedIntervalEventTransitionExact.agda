module DASHI.Core.TypedIntervalEventTransitionExact where

------------------------------------------------------------------------
-- TYPED INTERVAL / EVENT TRANSITIONS
--
-- REFERENCE / MOTIVATION
--
-- James F. Allen,
-- "Maintaining Knowledge about Temporal Intervals",
-- Communications of the ACM 26(11), 1983, 832-843.
-- DOI: 10.1145/182.358434.
--
-- Allen motivates qualitative interval relations.  This module deliberately
-- implements only the exact Nat interval fragment currently shared by LES,
-- Animalexic and SeaMeInIt: ordered intervals plus before/meets/overlaps.
-- The transitivity theorem below is a DASHI proof, not imported authority.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Nat using (_≤_; _<_)
open import Data.Nat.Properties as NatP using (<-trans; <-≤-trans)

record Interval : Set where
  constructor interval
  field
    startsAt : Nat
    endsAt : Nat
    ordered : startsAt ≤ endsAt

open Interval public

Before : Interval → Interval → Set
Before left right = endsAt left < startsAt right

Meets : Interval → Interval → Set
Meets left right = endsAt left ≡ startsAt right

record Overlaps (left right : Interval) : Set where
  constructor overlaps
  field
    leftStartsBeforeRight : startsAt left < startsAt right
    rightStartsBeforeLeftEnds : startsAt right < endsAt left
    leftEndsBeforeRightEnds : endsAt left < endsAt right

open Overlaps public

------------------------------------------------------------------------
-- `before` is transitive.  The middle interval's own well-formedness is the
-- bridge from its start to its end:
--
--   end(a) < start(b) ≤ end(b) < start(c).
------------------------------------------------------------------------

beforeTransitive :
  ∀ {first middle last} →
  Before first middle →
  Before middle last →
  Before first last
beforeTransitive {middle = middle} firstBeforeMiddle middleBeforeLast =
  NatP.<-trans
    (NatP.<-≤-trans firstBeforeMiddle (ordered middle))
    middleBeforeLast

------------------------------------------------------------------------
-- Event transitions keep interval evidence attached to the state change rather
-- than representing ordering as detached prose or a Boolean.
------------------------------------------------------------------------

record IntervalEventTransition (State Event : Set) : Set₁ where
  constructor intervalEventTransition
  field
    eventInterval : Event → Interval
    applyEvent : Event → State → State

open IntervalEventTransition public

record OrderedEventPair
    {State Event : Set}
    (system : IntervalEventTransition State Event)
    (first second : Event) : Set where
  constructor orderedEventPair
  field
    firstBeforeSecond :
      Before (eventInterval system first) (eventInterval system second)

open OrderedEventPair public

record TypedIntervalEventBoundary : Set where
  constructor typedIntervalEventBoundary
  field
    intervalsCarryOrderingWitness : Bool
    temporalRelationsAreProofRelevant : Bool
    beforeIsTransitive : Bool
    fullAllenCompositionTableNotClaimed : Bool
    physicalWorkflowMeaningRemainsDomainSpecific : Bool

canonicalTypedIntervalEventBoundary : TypedIntervalEventBoundary
canonicalTypedIntervalEventBoundary =
  typedIntervalEventBoundary true true true true true
