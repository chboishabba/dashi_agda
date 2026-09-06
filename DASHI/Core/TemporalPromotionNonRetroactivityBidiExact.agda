module DASHI.Core.TemporalPromotionNonRetroactivityBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.PromotionTransportChainBidiExact as Promotion
import DASHI.Core.BraidedRuntimeProofProvenanceBidiExact as RuntimeHistory

------------------------------------------------------------------------
-- APPEND-ONLY PROMOTION / TEMPORAL NON-RETROACTIVITY
--
-- Reverse x-pollination from Lean Integration.Kernel.AppendOnlyHistory plus
-- PromotionTransport, welded to the existing Agda runtime-history boundary.
-- A later receipt can extend what is known/transportable without becoming an
-- inhabitant of an earlier historical state.
------------------------------------------------------------------------

data Time : Set where earlier later : Time

data Receipt : Set where transportReceipt : Receipt

AvailableAt : Time → Receipt → Set
AvailableAt earlier transportReceipt = ⊥
AvailableAt later transportReceipt = ⊤

laterReceiptExists : AvailableAt later transportReceipt
laterReceiptExists = tt

laterReceiptWasNotAvailableEarlier : AvailableAt earlier transportReceipt → ⊥
laterReceiptWasNotAvailableEarlier receipt = receipt

record AppendOnlyReceiptHistory : Set₁ where
  constructor append-only-receipt-history
  field
    Event : Set
    presentAt : Time → Event → Set
    earlierPersists : ∀ event → presentAt earlier event → presentAt later event
    historyReference : String

open AppendOnlyReceiptHistory public

record TimedPromotionReceipt
    {Artifact Statement Target : Set}
    (frame : Promotion.PromotionTransportFrame Artifact Statement Target)
    (artifact : Artifact)
    (statement : Statement)
    (target : Target) : Set₁ where
  constructor timed-promotion-receipt
  field
    issuedAt : Time
    promotion : Promotion.FullPromotionReceipt frame artifact statement target
    receiptReference : String

open TimedPromotionReceipt public

------------------------------------------------------------------------
-- Exact logical boundary: issuance at `later` does not provide an inhabitant
-- of the earlier availability predicate.  Historical provenance is extended,
-- not rewritten.
------------------------------------------------------------------------

data LaterReceiptBackdatesEarlierPossession : Set where

laterReceiptDoesNotBackdateEarlierPossession :
  LaterReceiptBackdatesEarlierPossession → ⊥
laterReceiptDoesNotBackdateEarlierPossession ()

runtimeHistoryAlreadyRequiresAppendOnlyCorrection : Bool
runtimeHistoryAlreadyRequiresAppendOnlyCorrection =
  RuntimeHistory.correctionAppendsHistoryRatherThanRewritesIt
    RuntimeHistory.canonicalBraidedRuntimeProofBoundary

record TemporalPromotionBoundary : Set where
  constructor temporal-promotion-boundary
  field
    laterReceiptMayExtendCurrentState : Bool
    laterReceiptRewritesEarlierPossession : Bool
    appendOnlyHistoryCompatibleWithPromotionTransport : Bool

canonicalTemporalPromotionBoundary : TemporalPromotionBoundary
canonicalTemporalPromotionBoundary =
  temporal-promotion-boundary true false true
