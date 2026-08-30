module DASHI.Culture.JohnAnthonyBrownDocumentLineageExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- JOHN ANTHONY BROWN MANUSCRIPT LINEAGE
--
-- The project attributes the research programme to John Anthony Brown.
-- Drive revision metadata is kept separate from authorship: a file's last
-- modifier is not, by itself, an authorship theorem.
------------------------------------------------------------------------

data DocumentStage : Set where
  draft3 : DocumentStage
  trackedChanges : DocumentStage
  comparativeMixedMethodsProposal : DocumentStage

record BrownDocumentSnapshot : Set where
  constructor brown-document-snapshot
  field
    stage : DocumentStage
    attributedAuthor : String
    titleOrLabel : String
    driveId : String
    driveRevisionDate : String
    sourceRole : String
    authorshipBasis : String

open BrownDocumentSnapshot public

draft3Snapshot : BrownDocumentSnapshot
draft3Snapshot = brown-document-snapshot
  draft3
  "John Anthony Brown"
  "John Research Paper Draft 3.docx"
  "1AjGz-75JPXk-83s6F0g7mRKktSIxKPtH"
  "2023-03-31"
  "earlier study-design draft"
  "project attribution; Drive modifier metadata is not treated as authorship proof"

trackedChangesSnapshot : BrownDocumentSnapshot
trackedChangesSnapshot = brown-document-snapshot
  trackedChanges
  "John Anthony Brown"
  "Johns-Research-Paper_3_tracked changes.docx"
  "1NZXfi_x4PgZ0e0N3xzOoL-FAzS2GHLCS"
  "2023-04-01"
  "expanded tracked-changes interdisciplinary manuscript"
  "project attribution; Drive modifier metadata is not treated as authorship proof"

latestProposalSnapshot : BrownDocumentSnapshot
latestProposalSnapshot = brown-document-snapshot
  comparativeMixedMethodsProposal
  "John Anthony Brown"
  "Childhood Religious Coercion, Trauma, and Long-Term Psychosocial Outcomes — A Comparative Mixed-Methods Research Proposal"
  "145ar46yZeeyALjRj0xXRQTz7EyFDr86_XcjJiCAFdXA"
  "2026-08-09"
  "latest of the three supplied documents by Drive revision timestamp; source for current section/hypothesis/design audit"
  "project attribution; document content and revision history are source provenance, not independent empirical verification"

latestProposalAuthor : attributedAuthor latestProposalSnapshot ≡ "John Anthony Brown"
latestProposalAuthor = refl

latestProposalStage : stage latestProposalSnapshot ≡ comparativeMixedMethodsProposal
latestProposalStage = refl

------------------------------------------------------------------------
-- BIDI lineage: later drafting can refine scope/design without retroactively
-- proving or erasing earlier propositions.
------------------------------------------------------------------------

data LaterDraftPromotesEarlierClaimToFact : Set where

data LaterDraftErasesEarlierGenealogy : Set where

data DriveLastModifierPromotesAuthorship : Set where

laterDraftDoesNotPromoteEarlierClaimToFact :
  LaterDraftPromotesEarlierClaimToFact → ⊥
laterDraftDoesNotPromoteEarlierClaimToFact ()

laterDraftDoesNotEraseEarlierGenealogy :
  LaterDraftErasesEarlierGenealogy → ⊥
laterDraftDoesNotEraseEarlierGenealogy ()

driveLastModifierDoesNotPromoteAuthorship :
  DriveLastModifierPromotesAuthorship → ⊥
driveLastModifierDoesNotPromoteAuthorship ()

record DocumentLineageBoundary : Set where
  constructor document-lineage-boundary
  field
    latestChosenByRevisionTimestamp : Bool
    authorshipAndLastModifierCollapsed : Bool
    laterDraftAutomaticallyValidatesCitations : Bool
    earlierDraftsRemainGenealogicallyRelevant : Bool
    latestProposalControlsCurrentSectionManifest : Bool

canonicalDocumentLineageBoundary : DocumentLineageBoundary
canonicalDocumentLineageBoundary =
  document-lineage-boundary true false false true true
