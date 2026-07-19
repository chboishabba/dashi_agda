module DASHI.Interop.SensibLawOntologyTopologyTests where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using ([])

open import DASHI.Interop.SensibLawOntologyTopology

world-owned-by-shared-core : layerOwner worldArtefacts ≡ sharedCore
world-owned-by-shared-core = refl

case-layer-is-joint : layerOwner legalEpisodes ≡ joint
case-layer-is-joint = refl

norms-owned-by-sensiblaw : layerOwner normativeSources ≡ SensibLaw
norms-owned-by-sensiblaw = refl

sampleEvent : Event
sampleEvent =
  event (stableId "event:transaction:12345")
    (stableId "event-class:financial-transaction")
    "2026-07-19T10:00:00+10:00"
    "Transfer from a joint account"

sampleEvidence : EvidenceItem
sampleEvidence =
  evidence (stableId "evidence:bank-row:12345")
    "sha256:example"
    "text/csv"
    "2026-07-19T10:01:00+10:00"
    (stableId "receipt:bank-export:1")

sampleLink : EventEvidenceLink
sampleLink = attachEvidence sampleEvent sampleEvidence "supports-occurrence"

evidence-is-near-world-event :
  EventEvidenceLink.linkedEvent sampleLink ≡ Event.eventId sampleEvent
evidence-is-near-world-event = refl

candidate-is-not-canonical-link : ResolutionCandidate
candidate-is-not-canonical-link =
  resolutionCandidateRecord
    (stableId "entity-document:landlord")
    (stableId "entity-document:property-manager")
    []
    suggested

same-event-can-have-two-system-fibres :
  WrongTypeInterpretation.interpretedEvent tikangaInterpretation
  ≡ WrongTypeInterpretation.interpretedEvent auInterpretation
same-event-can-have-two-system-fibres = same-event-multi-system
