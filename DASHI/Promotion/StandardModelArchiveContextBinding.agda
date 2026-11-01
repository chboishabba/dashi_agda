module DASHI.Promotion.StandardModelArchiveContextBinding where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; []; _∷_)

------------------------------------------------------------------------
-- Standard Model archive-context binding.
--
-- This module records metadata for the prior-chat/context inputs pulled into
-- ~/chat_archive.sqlite for the SM/Higgs/Yukawa/CKM first-principles boundary.
-- It deliberately stores UUID/title/source/status/tag rows only; transcripts
-- remain outside Agda and none of these rows is theorem authority.

data ArchiveSource : Set where
  chatGPTOnline : ArchiveSource
  perplexityOnline : ArchiveSource

data ArchiveContextStatus : Set where
  resolvedOnlineThread : ArchiveContextStatus
  dbPulledMetadataOnly : ArchiveContextStatus

data ArchiveSourceState : Set where
  db-pulled-2026-06-07 : ArchiveSourceState

data StandardModelArchiveTopic : Set where
  Higgs : StandardModelArchiveTopic
  Yukawa : StandardModelArchiveTopic
  CKM : StandardModelArchiveTopic
  PMNS : StandardModelArchiveTopic
  hypercharge : StandardModelArchiveTopic
  anomaly : StandardModelArchiveTopic
  first-principles : StandardModelArchiveTopic

canonicalBoundaryTags : List StandardModelArchiveTopic
canonicalBoundaryTags =
  Higgs
  ∷ Yukawa
  ∷ CKM
  ∷ PMNS
  ∷ hypercharge
  ∷ anomaly
  ∷ first-principles
  ∷ []

record StandardModelArchiveContextRow : Set where
  field
    onlineUUID : String
    titleLabel : String
    status : ArchiveContextStatus
    source : ArchiveSource
    sourceLabel : String
    topicTags : List StandardModelArchiveTopic
    topicTagsAreCanonicalBoundary :
      topicTags ≡ canonicalBoundaryTags
    sourceState : ArchiveSourceState
    sourceStateIsCanonical :
      sourceState ≡ db-pulled-2026-06-07
    sourceStateLabel : String
    sourceStateLabelIsCanonical :
      sourceStateLabel ≡ "db-pulled-2026-06-07"
    transcriptEmbedded : Bool
    transcriptEmbeddedIsFalse :
      transcriptEmbedded ≡ false
    theoremAuthority : Bool
    theoremAuthorityIsFalse :
      theoremAuthority ≡ false

open StandardModelArchiveContextRow public

mkArchiveContextRow :
  String →
  String →
  ArchiveSource →
  String →
  StandardModelArchiveContextRow
mkArchiveContextRow uuid title src srcLabel =
  record
    { onlineUUID = uuid
    ; titleLabel = title
    ; status = resolvedOnlineThread
    ; source = src
    ; sourceLabel = srcLabel
    ; topicTags = canonicalBoundaryTags
    ; topicTagsAreCanonicalBoundary = refl
    ; sourceState = db-pulled-2026-06-07
    ; sourceStateIsCanonical = refl
    ; sourceStateLabel = "db-pulled-2026-06-07"
    ; sourceStateLabelIsCanonical = refl
    ; transcriptEmbedded = false
    ; transcriptEmbeddedIsFalse = refl
    ; theoremAuthority = false
    ; theoremAuthorityIsFalse = refl
    }

archiveContextRowCount :
  List StandardModelArchiveContextRow →
  Nat
archiveContextRowCount [] =
  zero
archiveContextRowCount (_ ∷ rows) =
  suc (archiveContextRowCount rows)

canonicalStandardModelArchiveContextRows :
  List StandardModelArchiveContextRow
canonicalStandardModelArchiveContextRows =
  mkArchiveContextRow
    "6b8e55b6-ace3-4380-b7b9-9665c7ce142b"
    "check/confirm the formalism... (attached)"
    perplexityOnline
    "perplexity resolver refresh"
  ∷ mkArchiveContextRow
    "8daefbbb-e5e4-4c27-92c2-9cf7e9de0aa3"
    "DASHI blocker/frontier context"
    perplexityOnline
    "perplexity live/download resolver"
  ∷ mkArchiveContextRow
    "6a1fe6db-d050-83ec-b6d6-3822402518ce"
    "DASHI NS Research Update"
    chatGPTOnline
    "chatgpt pull"
  ∷ mkArchiveContextRow
    "69e0cb8f-9984-8399-a5fe-d9dbffca71e3"
    "Dashi on Quantum Computing"
    chatGPTOnline
    "chatgpt pull"
  ∷ mkArchiveContextRow
    "690e6e7a-ccd0-8321-b456-d27dba931120"
    "Quantum field count"
    chatGPTOnline
    "chatgpt pull"
  ∷ mkArchiveContextRow
    "696dbd54-8818-8324-b66b-70e7bdf32d2b"
    "Branch - Formalism Bridging GR and MDL - LES"
    chatGPTOnline
    "chatgpt pull"
  ∷ mkArchiveContextRow
    "696ed143-2ddc-8324-9b6e-aced5c5954d8"
    "Branch - Branch - Branch - Formalism Bridging GR and MDL"
    chatGPTOnline
    "chatgpt live pull"
  ∷ mkArchiveContextRow
    "696ecfaa-d220-8320-b0c1-dc981a4fc58f"
    "Branch - Branch - Formalism Bridging GR and MDL"
    chatGPTOnline
    "chatgpt live pull"
  ∷ mkArchiveContextRow
    "6993e43a-2d98-8399-b48d-6411a028e04c"
    "Dashi Motifs Formalized"
    chatGPTOnline
    "chatgpt pull"
  ∷ []

canonicalResolvedOnlineThreadCountIsNine :
  archiveContextRowCount canonicalStandardModelArchiveContextRows ≡ 9
canonicalResolvedOnlineThreadCountIsNine =
  refl

archiveContextIsNotTheoremAuthority :
  (row : StandardModelArchiveContextRow) →
  theoremAuthority row ≡ false
archiveContextIsNotTheoremAuthority row =
  theoremAuthorityIsFalse row

canonicalArchiveContextIsNotTheoremAuthority :
  theoremAuthority
    (mkArchiveContextRow
      "6b8e55b6-ace3-4380-b7b9-9665c7ce142b"
      "check/confirm the formalism... (attached)"
      perplexityOnline
      "perplexity resolver refresh")
  ≡ false
canonicalArchiveContextIsNotTheoremAuthority =
  refl

canonicalArchiveContextSourceState :
  (row : StandardModelArchiveContextRow) →
  sourceState row ≡ db-pulled-2026-06-07
canonicalArchiveContextSourceState row =
  sourceStateIsCanonical row
