module DASHI.Culture.MissingDeceasedCustodyEventTimeMatrixExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- COMPARATIVE CUSTODY / EVENT-TIME MATRIX
------------------------------------------------------------------------

data EvidenceState : Set where
  owned : EvidenceState
  partial : EvidenceState
  notLocated : EvidenceState
  contradicted : EvidenceState
  notApplicable : EvidenceState


record CustodyEventTimeRow : Set where
  constructor custody-event-time-row
  field
    subject : String
    eventTimeRole : EvidenceState
    physicalCustody : EvidenceState
    digitalOrDataCustody : EvidenceState
    organisationalContinuity : EvidenceState
    sameCarrierSuccession : EvidenceState
    strongestCurrentReading : String

open CustodyEventTimeRow public

eskridgeRow : CustodyEventTimeRow
eskridgeRow = custody-event-time-row
  "Amy Eskridge"
  partial
  notLocated
  notLocated
  partial
  notLocated
  "Corporate authority and Institute team surface are source-backed, but technical IP, apparatus, notebooks/repositories and post-death asset disposition remain open."

maiwaldRow : CustodyEventTimeRow
maiwaldRow = custody-event-time-row
  "Frank Maiwald"
  owned
  owned
  partial
  owned
  partial
  "Same project, successor PI, overlapping collaborators and the same external Weber-group apparatus are source-backed; exact JPL calibration/qualification carrier transfer remains open."

mccaslandRow : CustodyEventTimeRow
mccaslandRow = custody-event-time-row
  "William Neil McCasland"
  partial
  notLocated
  notLocated
  owned
  notLocated
  "Pre-acquisition ATA Director of Technology role and the 2025 BlueHalo-to-AeroVironment acquisition are source-backed; exact post-close role/access/portfolio is not located."

hicksRow : CustodyEventTimeRow
hicksRow = custody-event-time-row
  "Michael David Hicks"
  contradicted
  notLocated
  notLocated
  partial
  notLocated
  "Institutional memorials end JPL service in 2022, before the 2023 death. Historical mission expertise is owned, but event-time JPL operational access cannot be inherited without a separate receipt."

loureiroRow : CustodyEventTimeRow
loureiroRow = custody-event-time-row
  "Nuno Loureiro"
  owned
  partial
  partial
  owned
  partial
  "Event-time MIT/PSFC role is strong, but science-specific event causation is independently pressured by authorities linking the same suspect to the Brown University mass shooting."

record MatrixBoundary : Set where
  constructor matrix-boundary
  field
    notLocatedImpliesAbsent : Bool
    notLocatedImpliesAbsentIsFalse : notLocatedImpliesAbsent ≡ false
    organisationalContinuityImpliesSameCarrierTransfer : Bool
    organisationalContinuityImpliesSameCarrierTransferIsFalse : organisationalContinuityImpliesSameCarrierTransfer ≡ false
    formerRoleImpliesEventTimeRole : Bool
    formerRoleImpliesEventTimeRoleIsFalse : formerRoleImpliesEventTimeRole ≡ false

canonicalMatrixBoundary : MatrixBoundary
canonicalMatrixBoundary = matrix-boundary false refl false refl false refl
