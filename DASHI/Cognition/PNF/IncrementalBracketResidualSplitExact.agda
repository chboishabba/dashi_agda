module DASHI.Cognition.PNF.IncrementalBracketResidualSplitExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Data.List.Base using (List)

import DASHI.Cognition.PNF.BracketedTSFVFractranWorldFibreExact as World
import DASHI.Cognition.PNF.SemanticConsumerMinimalExecutionExact as Minimal
import DASHI.Foundations.SSPTritCarrier as Trit

------------------------------------------------------------------------
-- A later predicate/bracket may split a previously retained consumer fibre.
-- The source worlds are not reconstructed or rewritten; only the observation
-- map is refined over the already-retained residual carrier.
------------------------------------------------------------------------

record ResidualDiscriminator : Set₁ where
  constructor residualDiscriminator
  field
    WorldCarrier : Set
    oldObserve : WorldCarrier → Trit.SSPTrit
    newObserve : WorldCarrier → Trit.SSPTrit
    history : WorldCarrier → World.WorldHistory

open ResidualDiscriminator public

record PreviouslyCollapsedPair
    (D : ResidualDiscriminator)
    (left right : WorldCarrier D)
    : Set where
  constructor previouslyCollapsedPair
  field
    oldObservationEqual : oldObserve D left ≡ oldObserve D right

open PreviouslyCollapsedPair public

record SplitByNewPredicate
    (D : ResidualDiscriminator)
    (left right : WorldCarrier D)
    : Set where
  constructor splitByNewPredicate
  field
    wasCollapsed : PreviouslyCollapsedPair D left right
    Distinguishable : Set
    distinction : Distinguishable

open SplitByNewPredicate public

record IncrementalSplitReceipt : Set₁ where
  constructor incrementalSplitReceipt
  field
    before : Minimal.ConsumerMinimalTokenState
    after : Minimal.ConsumerMinimalTokenState
    newPredicateAvailable : Bool
    sourceDocumentRebuilt : Bool
    retainedHistoryReused : Bool
    sourceDocumentRebuiltIsFalse : sourceDocumentRebuilt ≡ false
    retainedHistoryReusedIsTrue : retainedHistoryReused ≡ true

open IncrementalSplitReceipt public

record IncrementalSplitBoundary : Set where
  constructor incrementalSplitBoundary
  field
    newPredicateMustRewriteFineWorlds : Bool
    newPredicateMayRefineObservationOnly : Bool
    oldResidualHistoryMayBeReused : Bool
    oldObservationEqualityImpliesNewEquality : Bool

canonicalIncrementalSplitBoundary : IncrementalSplitBoundary
canonicalIncrementalSplitBoundary =
  incrementalSplitBoundary false true true false
