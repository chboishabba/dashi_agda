module DASHI.Core.HistoricalFirstFailureTraceBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.QueryPromotionResidualBidiExact as QueryPromotion
import DASHI.Core.PromotionResidualSelectiveReopeningBidiExact as Reopen
import DASHI.Core.TemporalStrandProvenanceBidiExact as TemporalStrand
import DASHI.Core.TemporalPromotionNonRetroactivityBidiExact as Temporal

------------------------------------------------------------------------
-- TEMPORAL STRAND PROVENANCE -> HISTORICAL FIRST FAILURE
--
-- Promotion failure is indexed by the status actually available at a time.
-- The first missing stage determines the reopen target, while a later receipt
-- does not rewrite which stage was historically missing earlier.
------------------------------------------------------------------------

record HistoricalPromotionSnapshot : Set₁ where
  constructor historical-promotion-snapshot
  field
    time : Temporal.Time
    status : QueryPromotion.PromotionStatus
    firstResidual : QueryPromotion.PromotionResidual
    firstResidualCorrect :
      firstResidual ≡ QueryPromotion.firstPromotionResidual status
    reopenTarget : Reopen.ReopenTarget
    reopenTargetCorrect :
      reopenTarget ≡ Reopen.targetForResidual firstResidual
    strandReceiptReference : String
    snapshotReference : String

open HistoricalPromotionSnapshot public

snapshotFor :
  Temporal.Time → QueryPromotion.PromotionStatus → String →
  HistoricalPromotionSnapshot
snapshotFor time status strandRef =
  historical-promotion-snapshot
    time
    status
    (QueryPromotion.firstPromotionResidual status)
    refl
    (Reopen.targetForResidual (QueryPromotion.firstPromotionResidual status))
    refl
    strandRef
    "historical first-missing-stage snapshot"

earlierMissingTransport : HistoricalPromotionSnapshot
earlierMissingTransport =
  snapshotFor Temporal.earlier
    (QueryPromotion.promotion-status true true false false)
    "transport receipt not yet available"

laterPromotionClosed : HistoricalPromotionSnapshot
laterPromotionClosed =
  snapshotFor Temporal.later
    (QueryPromotion.promotion-status true true true true)
    "later transport and target receipts available"

earlierFailureWasTransport :
  firstResidual earlierMissingTransport ≡ QueryPromotion.missingTransport
earlierFailureWasTransport = refl

laterStateReopensNothing :
  reopenTarget laterPromotionClosed ≡ Reopen.noReopen
laterStateReopensNothing = refl

------------------------------------------------------------------------
-- Historical non-retroactivity: later closure changes the later snapshot, not
-- the proposition describing the earlier first failure.
------------------------------------------------------------------------

data LaterClosureErasesEarlierFirstFailure : Set where
data LaterReceiptBackfillsEarlierStrandPossession : Set where

laterClosureDoesNotEraseEarlierFirstFailure :
  LaterClosureErasesEarlierFirstFailure → ⊥
laterClosureDoesNotEraseEarlierFirstFailure ()

laterReceiptDoesNotBackfillEarlierStrandPossession :
  LaterReceiptBackfillsEarlierStrandPossession → ⊥
laterReceiptDoesNotBackfillEarlierStrandPossession ()

strandHistoryStillNonRetroactive =
  TemporalStrand.laterTransportNotAvailableEarlier

record HistoricalFirstFailureBoundary : Set where
  constructor historical-first-failure-boundary
  field
    firstFailureIsTimeIndexed : Bool
    laterClosureMayChangeCurrentResidual : Bool
    laterClosureRewritesEarlierResidual : Bool
    historicalFailureDeterminesStageLocalReopen : Bool

canonicalHistoricalFirstFailureBoundary : HistoricalFirstFailureBoundary
canonicalHistoricalFirstFailureBoundary =
  historical-first-failure-boundary true true false true
