module DASHI.Visual.TemporalAxisExact where

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- TEMPORAL DISPLAY AXIS
--
-- Repository-history views place chronological time on the vertical axis and
-- branch-lane separation on the horizontal axis. Commit ordinal is not a
-- substitute for elapsed time.
------------------------------------------------------------------------

data HistoryAxisDimension : Set where
  horizontalBranchLane : HistoryAxisDimension
  verticalTime : HistoryAxisDimension

record TemporalAxisPolicy : Set where
  constructor temporalAxisPolicy
  field
    branchAxis : HistoryAxisDimension
    timeAxis : HistoryAxisDimension

    commitOrdinalDefinesTimePosition : Bool
    commitOrdinalDefinesTimePositionIsFalse :
      commitOrdinalDefinesTimePosition ≡ false

    timestampDefinesTimePosition : Bool
    timestampDefinesTimePositionIsTrue :
      timestampDefinesTimePosition ≡ true

open TemporalAxisPolicy public

canonicalTemporalAxisPolicy : TemporalAxisPolicy
canonicalTemporalAxisPolicy =
  temporalAxisPolicy
    horizontalBranchLane
    verticalTime
    false refl
    true refl

record TemporalAxisBoundary : Set where
  constructor temporalAxisBoundary
  field
    equalCommitCountImpliesEqualElapsedTime : Bool
    equalCommitCountImpliesEqualElapsedTimeIsFalse :
      equalCommitCountImpliesEqualElapsedTime ≡ false

    rendererMayReorderTimestampOrder : Bool
    rendererMayReorderTimestampOrderIsFalse :
      rendererMayReorderTimestampOrder ≡ false

canonicalTemporalAxisBoundary : TemporalAxisBoundary
canonicalTemporalAxisBoundary =
  temporalAxisBoundary
    false refl
    false refl
