module DASHI.Wikimedia.AristotleNativeModelSourceExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- SOURCE PIN: UPLOADED ARISTOTLE WIKIDATA/WIKI LEAN TRANCHE
--
-- Archive supplied in conversation:
--   ae06ae06-2580-422a-8fc3-92aeaaca8762-aristotle (2).tar.gz
-- SHA-256 rechecked 7 Sep 2026:
--   924400c414d9d7e3d416bded3a016a891e348ab3177d9d1552be669f1a72e455
--
-- Recheck found exactly 189 RequestProject/*.lean modules.  High-value native
-- donors include Engine, PropertyEngine, Snaks, Ranks, Qualifiers, Provenance,
-- Sitelinks, Lexemes, ExternalIds, Rdf, CompilerPipeline, Corpus*, Cli/*, Wiki/*.
--
-- Source boundary: this record pins methodology/data-model provenance and exact
-- declaration names inspected in the uploaded source.  It does not transport
-- Lean proofs into Agda or make the archive authoritative for live Wikidata.
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
    "uploaded Aristotle RequestProject native Wikidata/Wiki model; source rechecked 2026-09-07"
    false
    false

record AristotleDeclarationContract : Set where
  constructor aristotle-declaration-contract
  field
    sourceModule : String
    declarationName : String
    contractReading : String
open AristotleDeclarationContract public

engineKbContract : AristotleDeclarationContract
engineKbContract = aristotle-declaration-contract
  "RequestProject.Engine"
  "Wikidata.KB"
  "executable ontology kernel stores items, P279/sub, P31/inst, disjointness and level metadata"

propertyEngineContract : AristotleDeclarationContract
propertyEngineContract = aristotle-declaration-contract
  "RequestProject.PropertyEngine"
  "Wikidata.PKB"
  "general property statements form a separate layer over the ontology KB"

snakSatisfiabilityContract : AristotleDeclarationContract
snakSatisfiabilityContract = aristotle-declaration-contract
  "RequestProject.Snaks"
  "Wikidata.SnakBase.satisfiable_iff_clashFree"
  "snak-base satisfiability is equivalent to absence of value/someValue versus noValue clashes"

sitelinkRoundTripContract : AristotleDeclarationContract
sitelinkRoundTripContract = aristotle-declaration-contract
  "RequestProject.Sitelinks"
  "Wikidata.SiteKB.pageOf_eq_some_iff_itemOf_eq_some"
  "under functional/page-injective hypotheses, item-to-page and page-to-item lookup agree"

compiledInstancePreservationContract : AristotleDeclarationContract
compiledInstancePreservationContract = aristotle-declaration-contract
  "RequestProject.CompilerPipeline"
  "Wikidata.CompilerPipeline.compiled_inst"
  "compiler repair/pruning preserves the instance-edge list"

recheckedContracts : List AristotleDeclarationContract
recheckedContracts =
  engineKbContract
  ∷ propertyEngineContract
  ∷ snakSatisfiabilityContract
  ∷ sitelinkRoundTripContract
  ∷ compiledInstancePreservationContract
  ∷ []

data AristotleLeanProofIsAgdaProof : Set where
data AristotleArchiveIsLiveWikidataAuthority : Set where

a ristotleLeanProofDoesNotBecomeAgdaProof : AristotleLeanProofIsAgdaProof → ⊥
a ristotleLeanProofDoesNotBecomeAgdaProof ()

archiveDoesNotBecomeLiveWikidataAuthority : AristotleArchiveIsLiveWikidataAuthority → ⊥
archiveDoesNotBecomeLiveWikidataAuthority ()
