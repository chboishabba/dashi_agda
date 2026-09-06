module DASHI.Core.TemporalStrandProvenanceBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.BraidedEvidenceTraceBidiCrossPollination2026Exact as Braid
import DASHI.Core.TemporalPromotionNonRetroactivityBidiExact as Temporal

data StrandObligation : Set where
  artifactObligation correspondenceObligation transportObligation inhabitanceObligation : StrandObligation

record TimedStrandReceipt : Set where
  constructor timed-strand-receipt
  field
    strand : Braid.EvidenceStrand
    obligation : StrandObligation
    issuedAt : Temporal.Time
    receiptReference : String
open TimedStrandReceipt public

record TemporalStrandHistory : Set₁ where
  constructor temporal-strand-history
  field
    Receipt : Set
    receiptStrand : Receipt → Braid.EvidenceStrand
    receiptObligation : Receipt → StrandObligation
    availableAt : Temporal.Time → Receipt → Set
    earlierPersists : ∀ receipt → availableAt Temporal.earlier receipt → availableAt Temporal.later receipt
    historyReference : String
open TemporalStrandHistory public

transportStrand : Braid.EvidenceStrand
transportStrand = Braid.evidence-strand "transport-strand" Braid.proofWeft
  "synthetic transport source" "strand-local authority"

data ToyReceipt : Set where laterTransport : ToyReceipt

toyReceiptStrand : ToyReceipt → Braid.EvidenceStrand
toyReceiptStrand laterTransport = transportStrand
toyReceiptObligation : ToyReceipt → StrandObligation
toyReceiptObligation laterTransport = transportObligation
toyAvailableAt : Temporal.Time → ToyReceipt → Set
toyAvailableAt Temporal.earlier laterTransport = ⊥
toyAvailableAt Temporal.later laterTransport = ⊤
toyEarlierPersists : ∀ receipt → toyAvailableAt Temporal.earlier receipt → toyAvailableAt Temporal.later receipt
toyEarlierPersists laterTransport ()

toyTemporalStrandHistory : TemporalStrandHistory
toyTemporalStrandHistory = temporal-strand-history ToyReceipt toyReceiptStrand toyReceiptObligation
  toyAvailableAt toyEarlierPersists "synthetic append-only strand history"

laterTransportAvailable : availableAt toyTemporalStrandHistory Temporal.later laterTransport
laterTransportAvailable = tt
laterTransportNotAvailableEarlier : availableAt toyTemporalStrandHistory Temporal.earlier laterTransport → ⊥
laterTransportNotAvailableEarlier receipt = receipt

data LaterStrandReceiptRewritesEarlierStrandHistory : Set where
data ReceiptOnOneStrandTransfersAuthorityToAnother : Set where
laterStrandReceiptDoesNotRewriteEarlierHistory : LaterStrandReceiptRewritesEarlierStrandHistory → ⊥
laterStrandReceiptDoesNotRewriteEarlierHistory ()
oneStrandReceiptDoesNotTransferAuthority : ReceiptOnOneStrandTransfersAuthorityToAnother → ⊥
oneStrandReceiptDoesNotTransferAuthority ()

record TemporalStrandBoundary : Set where
  constructor temporal-strand-boundary
  field
    receiptsAreTimeIndexed : Bool
    laterReceiptMayExtendOneStrand : Bool
    laterReceiptBackfillsEarlierPossession : Bool
    strandLocalReceiptTransfersAuthority : Bool
canonicalTemporalStrandBoundary : TemporalStrandBoundary
canonicalTemporalStrandBoundary = temporal-strand-boundary true true false false
