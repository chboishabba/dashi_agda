module DASHI.Governance.OccupyArchivalObservationModelExact where

open import DASHI.Core.Prelude

import DASHI.Core.GenericReceipt as GenericReceipt

------------------------------------------------------------------------
-- ARCHIVAL OBSERVATION MODEL.
--
-- This owner separates three relations that are easy to collapse accidentally:
--
--   EventInteraction      -- what actually happened in the meeting
--   RecordMentions        -- what the surviving archival record reports
--   CodedEdge             -- what DASHI admits from that record
--
-- The current People's Library coding policy can be audited for coding fidelity
-- relative to the text it inspects.  That does not by itself establish that the
-- record is complete or perfectly faithful to every event in the meeting.
------------------------------------------------------------------------

record ObservationLayers
    (Participant Issue EventRecord CodedRecord : Set) : Set₁ where
  field
    EventInteraction : Participant → Issue → Set
    RecordMentions : EventRecord → Participant → Issue → Set
    CodedEdge : CodedRecord → Participant → Issue → Set

open ObservationLayers public

------------------------------------------------------------------------
-- Layer-specific witnesses.
------------------------------------------------------------------------

record CodingFidelity
    {Participant Issue EventRecord CodedRecord : Set}
    (layers : ObservationLayers Participant Issue EventRecord CodedRecord)
    (decodeSource : CodedRecord → EventRecord) : Set₁ where
  field
    codedEdgeHasRecordWitness :
      ∀ {coded participant issue} →
      CodedEdge layers coded participant issue →
      RecordMentions layers (decodeSource coded) participant issue

record DocumentarySoundness
    {Participant Issue EventRecord CodedRecord : Set}
    (layers : ObservationLayers Participant Issue EventRecord CodedRecord) : Set₁ where
  field
    recordedInteractionOccurred :
      ∀ {record participant issue} →
      RecordMentions layers record participant issue →
      EventInteraction layers participant issue

record DocumentaryCompleteness
    {Participant Issue EventRecord CodedRecord : Set}
    (layers : ObservationLayers Participant Issue EventRecord CodedRecord)
    (record : EventRecord) : Set₁ where
  field
    everyEventInteractionRecorded :
      ∀ {participant issue} →
      EventInteraction layers participant issue →
      RecordMentions layers record participant issue

------------------------------------------------------------------------
-- Conditional transport theorem.
--
-- A coded edge reaches event-level interaction only if we possess both coding
-- fidelity and documentary soundness.  Completeness is a separate property and
-- is not required for this one-way transport.
------------------------------------------------------------------------

codedEdgeToEventInteraction :
  ∀ {Participant Issue EventRecord CodedRecord : Set}
    {layers : ObservationLayers Participant Issue EventRecord CodedRecord}
    {decodeSource : CodedRecord → EventRecord} →
  CodingFidelity layers decodeSource →
  DocumentarySoundness layers →
  ∀ {coded participant issue} →
  CodedEdge layers coded participant issue →
  EventInteraction layers participant issue
codedEdgeToEventInteraction fidelity documentary coded =
  DocumentarySoundness.recordedInteractionOccurred documentary
    (CodingFidelity.codedEdgeHasRecordWitness fidelity coded)

------------------------------------------------------------------------
-- Completeness implication: only under an explicit completeness witness can
-- all event interactions be transported into the selected record.
------------------------------------------------------------------------

eventInteractionToRecordMention :
  ∀ {Participant Issue EventRecord CodedRecord : Set}
    {layers : ObservationLayers Participant Issue EventRecord CodedRecord}
    {record : EventRecord} →
  DocumentaryCompleteness layers record →
  ∀ {participant issue} →
  EventInteraction layers participant issue →
  RecordMentions layers record participant issue
eventInteractionToRecordMention completeness event =
  DocumentaryCompleteness.everyEventInteractionRecorded completeness event

------------------------------------------------------------------------
-- Promotion boundary.
------------------------------------------------------------------------

record ArchivalObservationBoundary : Set where
  constructor archivalObservationBoundary
  field
    codingFidelityIsDocumentaryCompleteness : Bool
    documentaryCompletenessAssumed : Bool
    documentarySoundnessAssumed : Bool
    codedEdgeAloneProvesEventInteraction : Bool
    omittedRecordMentionMeansEventDidNotOccur : Bool
    transportToEventRequiresCodingAndDocumentaryWitnesses : Bool

open ArchivalObservationBoundary public

canonicalObservationBoundary : ArchivalObservationBoundary
canonicalObservationBoundary =
  archivalObservationBoundary
    false
    false
    false
    false
    false
    true

canonicalOccupyArchivalObservationModelReceipt : GenericReceipt.GenericReceipt
canonicalOccupyArchivalObservationModelReceipt =
  GenericReceipt.mkNonPromotingReceipt
    "Occupy archival event-record-coding observation model"
    "DASHI.Governance.OccupyArchivalObservationModelExact"
    "canonicalObservationBoundary"
    "separates event interaction, archival record mention and DASHI-coded edge relations and proves conditional transport from coded edge to event interaction only when independent coding-fidelity and documentary-soundness witnesses are supplied"
    "current archive coding does not by itself establish documentary soundness or completeness; an omitted record mention cannot be promoted to non-occurrence, and event-level causal analysis must retain this measurement boundary"
    "agda -i . DASHI/Governance/OccupyArchivalObservationModelRegression.agda"
