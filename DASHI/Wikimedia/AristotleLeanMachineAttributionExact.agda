module DASHI.Wikimedia.AristotleLeanMachineAttributionExact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Wikimedia.AristotleNativeModelSourceExact as Aristotle

------------------------------------------------------------------------
-- ATTRIBUTION ENVELOPE FOR THE USER-SUPPLIED JMD / ARISTOTLE LEAN MACHINE
--
-- This owner does not invent a DOI, public URL, live-Wikidata authority or
-- cross-kernel proof transport.  It wraps the already-pinned uploaded archive
-- in the repository's canonical AttributedSourceCore so every downstream BIDI
-- receipt can retain exact source identity and archive digest provenance.
------------------------------------------------------------------------

archiveDigestUrn : String
archiveDigestUrn =
  "urn:sha256:924400c414d9d7e3d416bded3a016a891e348ab3177d9d1552be669f1a72e455"

jmdLeanArchiveSource : Source.AttributedSource
jmdLeanArchiveSource =
  Source.mkNoDOISource
    "JMD project archive (user-supplied attribution)"
    (Aristotle.archiveName Aristotle.canonicalAristotleWikimediaSource)
    "uploaded Aristotle RequestProject Lean/Wikidata machine archive"
    "2026"
    archiveDigestUrn
    (Source.namedSourceKind "user-supplied executable Lean/Wikidata project archive")
    "methodology and executable-model donor for getter/import/elaboration/typecheck/proof/report status; not live Wikidata authority and not proof transport into Agda"
    Source.publicAttribution

jmdLeanArchiveAtlas : Source.AttributedSourceAtlas
jmdLeanArchiveAtlas =
  Source.mkSourceAtlas
    "JMD / Aristotle Lean Wikidata machine source atlas"
    "DASHI.Wikimedia.AristotleLeanMachineAttributionExact"
    (jmdLeanArchiveSource ∷ [])
    "exact uploaded archive identity and SHA-256; no DOI supplied; source attribution imports neither proof nor authority"

------------------------------------------------------------------------
-- EXACT DECLARATION CONTRACTS RECHECKED IN THE PINNED ARCHIVE
--
-- These are attribution/source propositions only.  Naming the Lean declaration
-- neither imports its proof into Agda nor establishes that a live network call,
-- typecheck or kernel check has been executed in the current DASHI session.
------------------------------------------------------------------------

entityDataUrlContract : Aristotle.AristotleDeclarationContract
entityDataUrlContract =
  Aristotle.aristotle-declaration-contract
    "RequestProject.Cli.Fetch"
    "entityDataUrl"
    "constructs the Special:EntityData URL for a supplied Wikidata entity identifier"

fetchEntityJsonContract : Aristotle.AristotleDeclarationContract
fetchEntityJsonContract =
  Aristotle.aristotle-declaration-contract
    "RequestProject.Cli.Fetch"
    "fetchEntityJson"
    "uses the local entity cache or retrieves revision-unpromoted Wikidata EntityData JSON according to offline mode"

fetchEntityContract : Aristotle.AristotleDeclarationContract
fetchEntityContract =
  Aristotle.aristotle-declaration-contract
    "RequestProject.Cli.Fetch"
    "fetchEntity"
    "parses fetched entity JSON into the executable Wikidata entity representation"

scanArticleContract : Aristotle.AristotleDeclarationContract
scanArticleContract =
  Aristotle.aristotle-declaration-contract
    "RequestProject.Cli.Enrich"
    "scanArticle"
    "scans a Wikipedia article into source metadata including mentioned Wikidata items and external citations"

cmdEnrichContract : Aristotle.AristotleDeclarationContract
cmdEnrichContract =
  Aristotle.aristotle-declaration-contract
    "RequestProject.Cli.EnrichCmd"
    "cmdEnrich"
    "downloads selected missing terms and proposes source-tagged P279/P31 enrichment candidates"

cmdLeanContract : Aristotle.AristotleDeclarationContract
cmdLeanContract =
  Aristotle.aristotle-declaration-contract
    "RequestProject.Cli.Tool"
    "cmdLean"
    "compiles a knowledge base and its entailed facts into a Lean module; --kernel selects kernel decide rather than native_decide"

subChainSoundContract : Aristotle.AristotleDeclarationContract
subChainSoundContract =
  Aristotle.aristotle-declaration-contract
    "RequestProject.Cli.Derive"
    "checkSubChain_sound"
    "the executable subclass-chain checker has a soundness theorem connecting successful checks to derived subclass relations"

csvOfRowsContract : Aristotle.AristotleDeclarationContract
csvOfRowsContract =
  Aristotle.aristotle-declaration-contract
    "RequestProject.Reports"
    "csvOfRows / parseCsvText_csvOfRows"
    "renders witnessed diagnostic rows to CSV and proves the generated CSV parses back to the represented table"

worklistCsvContract : Aristotle.AristotleDeclarationContract
worklistCsvContract =
  Aristotle.aristotle-declaration-contract
    "RequestProject.Worklist"
    "worklistCsv / parseCsvText_worklistCsv"
    "renders the grouped diagnostic worklist as CSV with a proved parse-back contract"

jmdLeanMachineDeclarationContracts : List Aristotle.AristotleDeclarationContract
jmdLeanMachineDeclarationContracts =
  entityDataUrlContract
  ∷ fetchEntityJsonContract
  ∷ fetchEntityContract
  ∷ scanArticleContract
  ∷ cmdEnrichContract
  ∷ cmdLeanContract
  ∷ subChainSoundContract
  ∷ csvOfRowsContract
  ∷ worklistCsvContract
  ∷ []

record AristotleLeanMachineAttributionReceipt : Set where
  constructor aristotle-lean-machine-attribution-receipt
  field
    archiveReference : Aristotle.AristotleWikimediaSource
    attributedSource : Source.AttributedSource
    archiveIdentityPreserved : Bool
    archiveDigestPreserved : Bool
    archiveActsAsLiveWikidataAuthority : Bool
    archiveLeanProofBecomesAgdaProof : Bool

open AristotleLeanMachineAttributionReceipt public

jmdLeanArchiveAttributionReceipt : AristotleLeanMachineAttributionReceipt
jmdLeanArchiveAttributionReceipt =
  aristotle-lean-machine-attribution-receipt
    Aristotle.canonicalAristotleWikimediaSource
    jmdLeanArchiveSource
    true
    true
    false
    false

archiveIdentityPreservedTrue :
  archiveIdentityPreserved jmdLeanArchiveAttributionReceipt ≡ true
archiveIdentityPreservedTrue = refl

archiveDigestPreservedTrue :
  archiveDigestPreserved jmdLeanArchiveAttributionReceipt ≡ true
archiveDigestPreservedTrue = refl

archiveNotLiveWikidataAuthority :
  archiveActsAsLiveWikidataAuthority jmdLeanArchiveAttributionReceipt ≡ false
archiveNotLiveWikidataAuthority = refl

archiveLeanProofNotAgdaProof :
  archiveLeanProofBecomesAgdaProof jmdLeanArchiveAttributionReceipt ≡ false
archiveLeanProofNotAgdaProof = refl

sourceCitationDoesNotImportProof :
  Source.citationImportsProof jmdLeanArchiveSource ≡ false
sourceCitationDoesNotImportProof = Source.citationImportsProofIsFalse jmdLeanArchiveSource

sourceCitationDoesNotCreateAuthority :
  Source.citationCreatesAuthority jmdLeanArchiveSource ≡ false
sourceCitationDoesNotCreateAuthority = Source.citationCreatesAuthorityIsFalse jmdLeanArchiveSource
