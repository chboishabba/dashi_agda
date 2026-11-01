module DASHI.Interop.AristotleEvidenceSurfaceIdentityBoundaryExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- Archive donor: RequestProject.Publish / RequestProject.Archive.
--
-- Aristotle proves lossless JSONL publication and that canonical rendered text
-- determines a clean KB; it then uses a deterministic content address. SensibLaw
-- reuses the identity principle for evidence replay, not the exact hash function.
------------------------------------------------------------------------

record AristotlePublicationContract : Set where
  constructor aristotle-publication-contract
  field
    sourceModule : String
    declaration : String
    contractReference : String
open AristotlePublicationContract public

losslessPublicationContract : AristotlePublicationContract
losslessPublicationContract =
  aristotle-publication-contract
    "RequestProject.Publish"
    "Wikidata.Publish.parseJsonl?_jsonlOfKB"
    "the published JSON Lines carrier reads back to exactly the published knowledge base"

canonicalRenderIdentityContract : AristotlePublicationContract
canonicalRenderIdentityContract =
  aristotle-publication-contract
    "RequestProject.Publish"
    "Wikidata.Publish.eq_of_renderKB_eq"
    "for clean bases, equal canonical renderings determine equal knowledge bases"

archiveRoundTripContract : AristotlePublicationContract
archiveRoundTripContract =
  aristotle-publication-contract
    "RequestProject.Archive"
    "Wikidata.Archive.importKB?_bundleOf"
    "the archive bundle imports back to the deposited knowledge base"

record EvidenceSurfaceIdentityReceipt : Set where
  constructor evidence-surface-identity-receipt
  field
    canonicalRendererReference : String
    digestAlgorithmReference : String
    contentIdentityReference : String
    renderedContentReference : String
    identityScopeIsRenderedContentOnly : Bool
    identityScopeIsRenderedContentOnlyIsTrue : identityScopeIsRenderedContentOnly ≡ true
    truthAuthority : Bool
    truthAuthorityIsFalse : truthAuthority ≡ false
    revisionAlignmentAuthority : Bool
    revisionAlignmentAuthorityIsFalse : revisionAlignmentAuthority ≡ false
    promotionAuthority : Bool
    promotionAuthorityIsFalse : promotionAuthority ≡ false
open EvidenceSurfaceIdentityReceipt public

data SameContentIdImpliesSourceTruth : Set where
data SameContentIdImpliesRevisionAlignment : Set where
data ContentIdCreatesPromotionAuthority : Set where

contentIdentityDoesNotCreateSourceTruth : SameContentIdImpliesSourceTruth → ⊥
contentIdentityDoesNotCreateSourceTruth ()

contentIdentityDoesNotCreateRevisionAlignment : SameContentIdImpliesRevisionAlignment → ⊥
contentIdentityDoesNotCreateRevisionAlignment ()

contentIdentityDoesNotCreatePromotionAuthority : ContentIdCreatesPromotionAuthority → ⊥
contentIdentityDoesNotCreatePromotionAuthority ()

record EvidenceSurfaceIdentityBoundary : Set where
  constructor evidence-surface-identity-boundary
  field
    canonicalContentMayBeDeterministicallyNamed : Bool
    contentIdentityCreatesTruth : Bool
    contentIdentityCreatesRevisionAlignment : Bool
    contentIdentityCreatesPromotion : Bool

canonicalEvidenceSurfaceIdentityBoundary : EvidenceSurfaceIdentityBoundary
canonicalEvidenceSurfaceIdentityBoundary =
  evidence-surface-identity-boundary true false false false

evidenceSurfaceIdentityStatement : String
evidenceSurfaceIdentityStatement =
  "A canonical evidence surface may receive a deterministic content identity for replay and provenance. The identifier names rendered content only; it does not prove source truth, align graph and entity revisions, or create promotion/edit authority."
