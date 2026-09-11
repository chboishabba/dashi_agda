module DASHI.Policy.ABC730SourcePaidDiscourseRepairExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Policy.ABC730DiscourseRepairOverlayExact as Repair
import DASHI.Policy.ABC730PrimarySourceSpeakerResolutionExact as Source
import DASHI.Policy.ABC730WestBankSanctionsTranscriptClaimsExact as Transcript

------------------------------------------------------------------------
-- Composition of the discourse-repair overlay with later primary-source
-- speaker receipts.  Historical supplied-transcript state remains append-only;
-- this owner records what later evidence now pays.
------------------------------------------------------------------------

data RepairPaymentStatus : Set where
  unpaid : RepairPaymentStatus
  sourcePaid : RepairPaymentStatus
  sourceContradicted : RepairPaymentStatus
  notRequired : RepairPaymentStatus

record SourcePaidRepair : Set where
  constructor sourcePaidRepair
  field
    claimReference : String
    priorRepairReference : String
    sourceResolutionReference : String
    speakerPaymentStatus : RepairPaymentStatus
    resolvedSpeakerReference : String
    historicalRepairStatePreserved : Bool
    propositionTruthPromoted : Bool
    evaluativeTruthPromoted : Bool

open SourcePaidRepair public

c030SourcePaid : SourcePaidRepair
c030SourcePaid = sourcePaidRepair
  "ABC730-2026-09-09-C030"
  "ABC730DiscourseRepairOverlayExact.c030Repair"
  "ABC730PrimarySourceSpeakerResolutionExact.c030SpeakerResolution"
  sourcePaid
  "Ed Husic"
  true false false

c031SourcePaid : SourcePaidRepair
c031SourcePaid = sourcePaidRepair
  "ABC730-2026-09-09-C031"
  "ABC730DiscourseRepairOverlayExact.c031Repair"
  "ABC730PrimarySourceSpeakerResolutionExact.c031SpeakerResolution"
  sourcePaid
  "Ed Husic"
  true false false

c032SourcePaid : SourcePaidRepair
c032SourcePaid = sourcePaidRepair
  "ABC730-2026-09-09-C032"
  "ABC730DiscourseRepairOverlayExact.c032Repair"
  "ABC730PrimarySourceSpeakerResolutionExact.c032SpeakerResolution"
  sourcePaid
  "David Shoebridge"
  true false false

c033SourcePaid : SourcePaidRepair
c033SourcePaid = sourcePaidRepair
  "ABC730-2026-09-09-C033"
  "ABC730DiscourseRepairOverlayExact.c033Repair"
  "ABC730PrimarySourceSpeakerResolutionExact.c033SpeakerResolution"
  sourcePaid
  "Julian Leeser"
  true false false

bandtC032Contradicted : SourcePaidRepair
bandtC032Contradicted = sourcePaidRepair
  "ABC730-2026-09-09-C032"
  "AustraliaIsraelSanctionsAttributionExact.bandtSpeakerClaim"
  "ABC730PrimarySourceSpeakerResolutionExact.bandtC032Resolution"
  sourceContradicted
  "Adam Bandt"
  true false false

sourcePaidFrontier : List SourcePaidRepair
sourcePaidFrontier =
  c030SourcePaid ∷ c031SourcePaid ∷ c032SourcePaid ∷ c033SourcePaid ∷ bandtC032Contradicted ∷ []

------------------------------------------------------------------------
-- High-value policy coordinates remain independent.
------------------------------------------------------------------------

canonicalUKImportBan : Transcript.TranscriptClaim
canonicalUKImportBan = Transcript.abcUKImportBanClaim

canonicalAustraliaNoBlanketBan : Transcript.TranscriptClaim
canonicalAustraliaNoBlanketBan = Transcript.abcAustraliaNoBlanketBanClaim

canonicalAustraliaUnintendedConsequences : Transcript.TranscriptClaim
canonicalAustraliaUnintendedConsequences = Transcript.abcAustraliaUnintendedConsequencesRationale

canonicalGaslightingWords : Transcript.TranscriptClaim
canonicalGaslightingWords = Transcript.abcLaborGaslightingClaim

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data SourcePaidSpeakerRewritesPriorUnresolvedState : Set where
sourcePaidSpeakerDoesNotRewritePriorUnresolvedState : SourcePaidSpeakerRewritesPriorUnresolvedState → ⊥
sourcePaidSpeakerDoesNotRewritePriorUnresolvedState ()

data SourcePaidSpeakerPaysGaslightingTruth : Set where
sourcePaidSpeakerDoesNotPayGaslightingTruth : SourcePaidSpeakerPaysGaslightingTruth → ⊥
sourcePaidSpeakerDoesNotPayGaslightingTruth ()

data SourcePaidSpeakerPaysPolicyEffectiveness : Set where
sourcePaidSpeakerDoesNotPayPolicyEffectiveness : SourcePaidSpeakerPaysPolicyEffectiveness → ⊥
sourcePaidSpeakerDoesNotPayPolicyEffectiveness ()

record SourcePaidRepairBoundary : Set where
  constructor sourcePaidRepairBoundary
  field
    speakerResolutionCanAdvance : Bool
    historicalUnresolvedReceiptRetained : Bool
    propositionTextUnchanged : Bool
    evaluativeTruthStillIndependent : Bool
    policyEffectivenessStillIndependent : Bool

canonicalSourcePaidRepairBoundary : SourcePaidRepairBoundary
canonicalSourcePaidRepairBoundary =
  sourcePaidRepairBoundary true true true true true

priorRepairBoundaryAnchor : Repair.ABC730DiscourseRepairBoundary
priorRepairBoundaryAnchor = Repair.canonicalABC730DiscourseRepairBoundary

sourceBoundaryAnchor : Source.PrimarySourceResolutionBoundary
sourceBoundaryAnchor = Source.canonicalPrimarySourceResolutionBoundary
