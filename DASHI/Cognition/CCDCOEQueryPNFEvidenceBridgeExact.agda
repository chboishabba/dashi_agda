module DASHI.Cognition.CCDCOEQueryPNFEvidenceBridgeExact where

-- Query-indexed assessment on the SAME four-episode architecture as
-- CCDCOECognitiveMultiplexInvariantExact. Exact PNF is consumed as evidence
-- with an explicit application-supplied claim-link witness. No observation,
-- validity or threat classification is invented here.

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Cognition.CCDCOECognitiveMultiplexInvariantExact as C
import DASHI.Core.QueryIndexedProjectionAdequacyExact as Q
import DASHI.Core.IntersectionalNonFactorability as NF
import DASHI.Core.AttributedSourceCore as Source
import DASHI.Cognition.PNF.EventAlgebra as PNF

data Question : Set where
  outwardFunctionQuestion : Question
  interlayerIntegrityQuestion : Question
  provenanceQuestion : Question

data Answer : Set where
  functioningAnswer : Answer
  connectedAnswer : Answer
  severedAnswer : Answer
  organicAnswer : Answer
  influenceAnswer : Answer

outwardEpisode : C.Episode → C.OutwardReport
outwardEpisode e = C.outward (C.episodeArchitecture e)

reply : Question → C.Episode → Answer
reply outwardFunctionQuestion _ = functioningAnswer
reply interlayerIntegrityQuestion C.organicCoupled = connectedAnswer
reply interlayerIntegrityQuestion C.organicCut = severedAnswer
reply interlayerIntegrityQuestion C.influenceCoupled = connectedAnswer
reply interlayerIntegrityQuestion C.influenceCut = severedAnswer
reply provenanceQuestion C.organicCoupled = organicAnswer
reply provenanceQuestion C.organicCut = organicAnswer
reply provenanceQuestion C.influenceCoupled = influenceAnswer
reply provenanceQuestion C.influenceCut = influenceAnswer

semantics : Q.QuerySemantics C.Episode Question Answer
semantics = Q.querySemantics reply

functionQueryIsAdequate :
  Q.AdequateFor outwardEpisode semantics outwardFunctionQuestion
functionQueryIsAdequate =
  Q.factorsForQuery
    {project = outwardEpisode}
    {semantics = semantics}
    {query = outwardFunctionQuestion}
    (λ _ → functioningAnswer)
    (λ _ → refl)

integrityAnswerDiffers :
  connectedAnswer ≡ severedAnswer → ⊥
integrityAnswerDiffers ()

integrityDefect :
  Q.QueryAdequacyDefect
    outwardEpisode semantics interlayerIntegrityQuestion
integrityDefect =
  Q.queryAdequacyDefect
    {project = outwardEpisode}
    {semantics = semantics}
    {query = interlayerIntegrityQuestion}
    C.organicCoupled C.organicCut refl integrityAnswerDiffers

outwardCannotAnswerIntegrity :
  Q.AdequateFor
    outwardEpisode semantics interlayerIntegrityQuestion → ⊥
outwardCannotAnswerIntegrity =
  Q.queryAdequacyDefectBlocksFactorisation integrityDefect

originAnswerDiffers :
  organicAnswer ≡ influenceAnswer → ⊥
originAnswerDiffers ()

originDefect :
  Q.QueryAdequacyDefect
    outwardEpisode semantics provenanceQuestion
originDefect =
  Q.queryAdequacyDefect
    {project = outwardEpisode}
    {semantics = semantics}
    {query = provenanceQuestion}
    C.organicCut C.influenceCut refl originAnswerDiffers

outwardCannotAnswerProvenance :
  Q.AdequateFor outwardEpisode semantics provenanceQuestion → ⊥
outwardCannotAnswerProvenance =
  Q.queryAdequacyDefectBlocksFactorisation originDefect

-- Renaming, scoring or visually recharting the same observation cannot
-- recover a distinction erased by the outward observer.
rechartingCannotRecoverIntegrity :
  ∀ {Recharted : Set} →
  (rechart : C.OutwardReport → Recharted) →
  NF.FactorsThrough
    (λ episode → rechart (outwardEpisode episode))
    (reply interlayerIntegrityQuestion) →
  ⊥
rechartingCannotRecoverIntegrity rechart =
  NF.rechartingCannotRecoverErasedPhenomenon
    rechart integrityDefect

rechartingCannotRecoverProvenance :
  ∀ {Recharted : Set} →
  (rechart : C.OutwardReport → Recharted) →
  NF.FactorsThrough
    (λ episode → rechart (outwardEpisode episode))
    (reply provenanceQuestion) →
  ⊥
rechartingCannotRecoverProvenance rechart =
  NF.rechartingCannotRecoverErasedPhenomenon
    rechart originDefect

-- Real PNF events are required, not invented. In particular About must
-- be supplied by a source-specific, externally inspected correspondence
-- between an event, an episode and the actual consumer question.
record EvidenceOf
  (About : PNF.EventPNF → C.Episode → Question → Set)
  (episode : C.Episode)
  (question : Question) : Set where
  constructor evidenceOf
  field
    source : Source.AttributedSource
    candidate : PNF.CandidatePNF
    aboutEpisodeAndQuestion :
      About (PNF.event candidate) episode question

open EvidenceOf public

evidenceRemainsCandidate :
  ∀ {About episode question} →
  (evidence : EvidenceOf About episode question) →
  PNF.candidateOnly (candidate evidence) ≡ true
evidenceRemainsCandidate evidence =
  PNF.candidateOnlyIsTrue (candidate evidence)

-- PNF preserves full event provenance and temporal coordinates; their
-- existence is NOT evidence that this hypothetical case actually happened.
sourceEvent : ∀ {About episode question} →
  EvidenceOf About episode question → PNF.EventPNF
sourceEvent evidence = PNF.event (candidate evidence)

eventTime : ∀ {About episode question} →
  EvidenceOf About episode question → String
eventTime evidence = PNF.eventTime (sourceEvent evidence)

observationTime : ∀ {About episode question} →
  EvidenceOf About episode question → String
observationTime evidence = PNF.observationTime (sourceEvent evidence)

revisionRetainsOldEvent :
  (old new : PNF.EventPNF) →
  (kind : PNF.RevisionKind) →
  (receipt : String) →
  PNF.oldVersionRetained
    (PNF.revisePNF old new kind receipt) ≡ true
revisionRetainsOldEvent old new kind receipt =
  PNF.oldVersionRetainedIsTrue
    (PNF.revisePNF old new kind receipt)

-- Admissibility and source validity are deliberately external to the
-- structural witness. They cannot be created by the graph theorem alone.
