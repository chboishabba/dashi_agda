module DASHI.Wikimedia.AristotleLeanMachineAttributionExact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
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
