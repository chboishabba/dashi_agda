module DASHI.Governance.JusticeProvenanceOutcomeLensExact where

------------------------------------------------------------------------
-- JUSTICE PROVENANCE / PUBLIC-OUTCOME LENS
--
-- Public institutional outcome labels are a coarse surface.  Fine justice
-- provenance may include authority, chronology, refusal, route, future-safety
-- and evidence distinctions that are not reconstructible from that surface.
--
-- This module does not introduce a new lens calculus.  It instantiates the
-- existing DASHI.Core.FibreRestrictionCore and ProvenanceBearingQuotient:
-- surface-only reconstruction is impossible on an exact collision, while an
-- explicit proof-relevant receipt makes reopening exact.
--
-- No external source is attributed to this finite theorem.  It is a DASHI-local
-- specialization of the existing provenance-bearing quotient architecture.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Core.FibreRestrictionCore as Fibre
import DASHI.Core.ProvenanceBearingQuotient as Provenance

------------------------------------------------------------------------
-- Two fine justice states share one public institutional outcome.
------------------------------------------------------------------------

data FineJusticeRecord : Set where
  authorityPreservingRecord authorityViolatingRecord : FineJusticeRecord

data PublicOutcome : Set where
  interventionRecorded : PublicOutcome

publicOutcome : FineJusticeRecord → PublicOutcome
publicOutcome authorityPreservingRecord = interventionRecorded
publicOutcome authorityViolatingRecord = interventionRecorded

fineJusticeRecordsDiffer :
  authorityPreservingRecord ≡ authorityViolatingRecord → ⊥
fineJusticeRecordsDiffer ()

publicOutcomeCollision :
  publicOutcome authorityPreservingRecord
  ≡ publicOutcome authorityViolatingRecord
publicOutcomeCollision = refl

record ExactSurfaceReconstruction : Set₁ where
  constructor exactSurfaceReconstruction
  field
    reconstruct : PublicOutcome → FineJusticeRecord
    exact : (record : FineJusticeRecord) →
      reconstruct (publicOutcome record) ≡ record

open ExactSurfaceReconstruction public

publicOutcomeCannotReconstructFullJusticeState :
  ExactSurfaceReconstruction → ⊥
publicOutcomeCannotReconstructFullJusticeState reconstruction =
  fineJusticeRecordsDiffer
    (trans
      (sym (exact reconstruction authorityPreservingRecord))
      (trans
        (cong (reconstruct reconstruction) publicOutcomeCollision)
        (exact reconstruction authorityViolatingRecord)))

------------------------------------------------------------------------
-- Existing provenance-bearing quotient instantiated with an explicit receipt.
------------------------------------------------------------------------

data JusticeReceipt : Set where
  preservingReceipt violatingReceipt : JusticeReceipt

receiptFor : FineJusticeRecord → JusticeReceipt
receiptFor authorityPreservingRecord = preservingReceipt
receiptFor authorityViolatingRecord = violatingReceipt

reopenJustice : PublicOutcome → JusticeReceipt → FineJusticeRecord
reopenJustice outcome preservingReceipt = authorityPreservingRecord
reopenJustice outcome violatingReceipt = authorityViolatingRecord

justiceFibreCore : Fibre.FibreRestrictionCore
justiceFibreCore = record
  { Carrier = FineJusticeRecord
  ; Surface = PublicOutcome
  ; Evidence = JusticeReceipt
  ; project = publicOutcome
  ; Fibre = λ outcome → FineJusticeRecord
  ; restrictsFibre = λ receipt outcome → ⊤
  ; doesNotRecoverCarrier = true
  ; promotesTruth = false
  }

justiceProvenanceBearingQuotient :
  Provenance.ProvenanceBearingQuotient justiceFibreCore
justiceProvenanceBearingQuotient =
  Provenance.provenanceBearingQuotient
    JusticeReceipt
    receiptFor
    reopenJustice
    reopenExact
  where
  reopenExact :
    (record : FineJusticeRecord) →
    reopenJustice (publicOutcome record) (receiptFor record) ≡ record
  reopenExact authorityPreservingRecord = refl
  reopenExact authorityViolatingRecord = refl

proofRelevantReceiptReopensFineJusticeState :
  (record : FineJusticeRecord) →
  Provenance.reopen justiceProvenanceBearingQuotient
    (Fibre.project justiceFibreCore record)
    (Provenance.receipt justiceProvenanceBearingQuotient record)
  ≡ record
proofRelevantReceiptReopensFineJusticeState =
  Provenance.reopenExact justiceProvenanceBearingQuotient

projectionReceiptStillDoesNotAuthoriseSemanticErasure :
  Provenance.ProjectionSemanticErasurePermission
    Provenance.projectionReceiptOnly →
  ⊥
projectionReceiptStillDoesNotAuthoriseSemanticErasure =
  Provenance.projectionReceiptCannotEraseSemantics

record JusticeProvenanceOutcomeBoundary : Set where
  constructor justiceProvenanceOutcomeBoundary
  field
    publicOutcomeDeterminesFullJusticeState : Bool
    proofRelevantReceiptCanEnableExactReopening : Bool
    exactReopeningMakesProjectionSemanticallyComplete : Bool
    projectionReceiptCreatesJusticeAuthority : Bool

canonicalJusticeProvenanceOutcomeBoundary : JusticeProvenanceOutcomeBoundary
canonicalJusticeProvenanceOutcomeBoundary =
  justiceProvenanceOutcomeBoundary false true false false
