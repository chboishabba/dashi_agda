module DASHI.Wikimedia.SourceProvenanceExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- SOURCE / ATTRIBUTION CONSTITUTION FOR NATIVE WIKIMEDIA DATA
--
-- Repository authority: Docs/SourceAttributionPolicy.md.
-- The source layer is part of the typed claim boundary, not citation ornament.
------------------------------------------------------------------------

data SourceLayer : Set where
  wikidataStatementLayer : SourceLayer
  wikidataReferenceLayer : SourceLayer
  wikipediaRevisionLayer : SourceLayer
  externalReferencedSourceLayer : SourceLayer
  dashiReconstructionLayer : SourceLayer
  dashiInferenceLayer : SourceLayer
  dashiTheoremLayer : SourceLayer
  promotionAdjudicationLayer : SourceLayer


record SourceReceipt : Set where
  constructor sourceReceipt
  field
    layer : SourceLayer
    sourceReference : String
    stableIdentifier : String
    versionReference : String
    sourceContentHash : String
    sourceBoundary : String
open SourceReceipt public

record WikipediaRevisionReceipt : Set where
  constructor wikipediaRevisionReceipt
  field
    wikipediaSite : String
    wikipediaPageTitle : String
    wikipediaPageId : String
    wikipediaRevisionId : String
    wikipediaPermanentReference : String
    wikipediaContentHash : String
open WikipediaRevisionReceipt public

record WikidataSnapshotReceipt : Set where
  constructor wikidataSnapshotReceipt
  field
    wikidataEntityId : String
    wikidataRevisionReference : String
    wikidataRetrievalReference : String
    wikidataContentHash : String
open WikidataSnapshotReceipt public

-- P143/imported-from style provenance is intentionally not authority.
data ProvenanceIsAuthority : Set where
data WikipediaSentenceIsWikidataStatement : Set where
data ExternalDatumIsDashiTheorem : Set where
data DashiInferenceIsExternalSourceClaim : Set where

provenanceDoesNotCreateAuthority : ProvenanceIsAuthority → ⊥
provenanceDoesNotCreateAuthority ()

wikipediaSentenceIsNotWikidataStatement : WikipediaSentenceIsWikidataStatement → ⊥
wikipediaSentenceIsNotWikidataStatement ()

externalDatumDoesNotBecomeDashiTheorem : ExternalDatumIsDashiTheorem → ⊥
externalDatumDoesNotBecomeDashiTheorem ()

dashIInferenceDoesNotBecomeExternalClaim : DashiInferenceIsExternalSourceClaim → ⊥
dashIInferenceDoesNotBecomeExternalClaim ()

record SourceAttributionBoundary : Set where
  constructor source-attribution-boundary
  field
    sourceLayerTyped : Bool
    provenanceCreatesAuthority : Bool
    wikipediaSentenceEqualsWikidataStatement : Bool
    externalDatumEqualsDashiTheorem : Bool
    reconstructionInferencePromotionRemainDistinct : Bool

canonicalSourceAttributionBoundary : SourceAttributionBoundary
canonicalSourceAttributionBoundary =
  source-attribution-boundary true false false false true
