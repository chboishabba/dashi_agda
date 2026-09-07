module DASHI.Wikimedia.AristotleNativeModelSourceExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- SOURCE PIN: UPLOADED ARISTOTLE WIKIDATA/WIKI LEAN TRANCHE
--
-- Archive supplied in conversation:
--   ae06ae06-2580-422a-8fc3-92aeaaca8762-aristotle (2).tar.gz
-- SHA-256:
--   924400c414d9d7e3d416bded3a016a891e348ab3177d9d1552be669f1a72e455
--
-- Inspection found 189 RequestProject/*.lean modules.  High-value native-model
-- donors include Engine, PropertyEngine, Snaks, Ranks, Qualifiers, Provenance,
-- Sitelinks, Lexemes, ExternalIds, Rdf, Corpus*, Cli/Fetch, Cli/Import and Wiki/*.
--
-- Source boundary: this record pins methodology/data-model provenance.  It does
-- not transport Lean proofs into Agda or make the archive authoritative for
-- live Wikidata beyond the bounded source contracts actually checked.
------------------------------------------------------------------------

record AristotleWikimediaSource : Set where
  constructor aristotle-wikimedia-source
  field
    archiveName : String
    archiveSha256 : String
    leanModuleCount : Nat
    sourceReference : String
    proofTransportedToAgda : Bool
    liveWikidataAuthority : Bool
open AristotleWikimediaSource public

canonicalAristotleWikimediaSource : AristotleWikimediaSource
canonicalAristotleWikimediaSource =
  aristotle-wikimedia-source
    "ae06ae06-2580-422a-8fc3-92aeaaca8762-aristotle (2).tar.gz"
    "924400c414d9d7e3d416bded3a016a891e348ab3177d9d1552be669f1a72e455"
    189
    "uploaded Aristotle RequestProject native Wikidata/Wiki model"
    false
    false

data AristotleLeanProofIsAgdaProof : Set where
data AristotleArchiveIsLiveWikidataAuthority : Set where

aristotleLeanProofDoesNotBecomeAgdaProof : AristotleLeanProofIsAgdaProof → ⊥
aristotleLeanProofDoesNotBecomeAgdaProof ()

archiveDoesNotBecomeLiveWikidataAuthority : AristotleArchiveIsLiveWikidataAuthority → ⊥
archiveDoesNotBecomeLiveWikidataAuthority ()
