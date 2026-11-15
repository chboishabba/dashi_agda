module DASHI.Governance.EpistemicPowerSourceAtlasExact where

-- Source identity and attribution boundaries for the new finite models.
-- Authored interpretation receipts are not source-text verification, and
-- source metadata cannot prove either an empirical or a normative claim.
open import DASHI.Core.Prelude
import DASHI.Core.AttributedSourceCore as Attr

satta2024 : Attr.AttributedSource
satta2024 = Attr.mkDOISource
  "Mark Satta"
  "Epistemic Exhaustion and the Retention of Power"
  "Hypatia 39(3), 510-529"
  "2024"
  "10.1017/hyp.2024.1"
  "https://www.cambridge.org/core/journals/hypatia/article/epistemic-exhaustion-and-the-retention-of-power/D53FD093288CDC9DAAB02DE4C0740ACE"
  Attr.academicArticleSource
  "Original DASHI finite workload and history model; no attribution of theorem to author"
  Attr.publicAttribution

tuckYang2012 : Attr.AttributedSource
tuckYang2012 = Attr.mkNoDOISource
  "Eve Tuck and K. Wayne Yang"
  "Decolonization Is Not a Metaphor"
  "Decolonization: Indigeneity, Education and Society 1(1), 1-40"
  "2012"
  "https://ikdll.nau.edu/id/eprint/84/"
  Attr.academicArticleSource
  "Distinct decolonial commitments motivate non-substitution countermodels; no claim of complete operationalization"
  Attr.publicAttribution

epistemicPowerSources : Attr.AttributedSourceAtlas
epistemicPowerSources = Attr.mkSourceAtlas
  "Epistemic power and decolonial non-substitution source atlas"
  "DASHI Governance"
  (satta2024 ∷ tuckYang2012 ∷ [])
  "Two paper-level attributions, restricted to metadata and explicitly labelled interpretation"

sourceAtlasIsNonPromoting :
  (validation : String) →
  Attr.atlasCreatesAuthority epistemicPowerSources ≡ false
sourceAtlasIsNonPromoting validation = refl

data InterpretiveTopic : Set where
  beliefDetermination beliefRetention beliefCommunication : InterpretiveTopic
  materialRepatriation settlerMovesToInnocence incommensurability : InterpretiveTopic

data SourceStatus : Set where
  metadataRecorded passageLocated primaryPassageChecked : SourceStatus

record SourceBoundReading (source : Attr.AttributedSource) : Set where
  constructor source-bound-reading
  field
    originalSource : Attr.AttributedSource
    sourceIdentity : originalSource ≡ source
    location : String
    topic : InterpretiveTopic
    interpretation : String
    validationStatus : SourceStatus

open SourceBoundReading public

sattaDeterminationReading : SourceBoundReading satta2024
sattaDeterminationReading = source-bound-reading
  satta2024 refl
  "The nature of epistemic exhaustion, discussion following definition"
  beliefDetermination
  "Satta identifies effort to determine belief as one of three epistemic activities"
  passageLocated

sattaRetentionReading : SourceBoundReading satta2024
sattaRetentionReading = source-bound-reading
  satta2024 refl
  "The nature of epistemic exhaustion, paragraph on previously settled belief"
  beliefRetention
  "Satta distinguishes the effort of maintaining a belief under pressure to reopen it"
  passageLocated

sattaCommunicationReading : SourceBoundReading satta2024
sattaCommunicationReading = source-bound-reading
  satta2024 refl
  "The nature of epistemic exhaustion, paragraph on communicating beliefs"
  beliefCommunication
  "Satta distinguishes communicating and explaining a belief as a source of effort"
  passageLocated

tuckYangMaterialReading : SourceBoundReading tuckYang2012
tuckYangMaterialReading = source-bound-reading
  tuckYang2012 refl
  "2012 paper, abstract, page 1"
  materialRepatriation
  "Land and Indigenous life repatriation cannot be replaced by a general inclusion indicator"
  passageLocated

tuckYangInnocenceReading : SourceBoundReading tuckYang2012
tuckYangInnocenceReading = source-bound-reading
  tuckYang2012 refl
  "2012 paper, abstract, page 1"
  settlerMovesToInnocence
  "Metaphorical decolonization may function as evasion that preserves settler futurity"
  passageLocated

tuckYangIncommensurabilityReading : SourceBoundReading tuckYang2012
tuckYangIncommensurabilityReading = source-bound-reading
  tuckYang2012 refl
  "2012 paper, abstract, page 1"
  incommensurability
  "Social justice and decolonial goals may be incommensurable rather than numerically interchangeable"
  passageLocated

-- Explicit wrong-source substitution cannot be silently accepted:
-- a reading on one source must supply equality to the required source.
record SameSourceInterpretation
  (source : Attr.AttributedSource) : Set where
  constructor same-source-interpretation
  field
    reading : SourceBoundReading source
    aSource : Attr.AttributedSource
    matches : aSource ≡ source
