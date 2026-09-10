module DASHI.Core.SnowballAttributionProvenanceInvariantExact where

open import DASHI.Core.Prelude
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Core.SnowballPluralLensInvariantExact as Lens

------------------------------------------------------------------------
-- ATTRIBUTION / PROVENANCE AS A SNOWBALL INSTANCE
--
-- AttributedSourceCore and the plural lens are slightly different surfaces:
-- the former names source identity/role/visibility; the latter requires every
-- locally relevant coordinate to survive projection. This module makes source
-- role one concrete instantiation of the abstract invariant.
------------------------------------------------------------------------

data AttributionAxis : Set where
  authorAxis titleAxis publicationAxis doiAxis canonicalURLAxis sourceKindAxis
  formalisationRelationshipAxis visibilityAxis proofImportAxis authorityAxis : AttributionAxis

attributionRelevant : AttributionAxis → Bool
attributionRelevant _ = true

attributionRetained : AttributionAxis → Bool
attributionRetained _ = true

canonicalAttributionLens : Lens.PluralLens AttributionAxis
canonicalAttributionLens = Lens.plural-lens attributionRelevant attributionRetained (λ _ _ → refl)

record SourceRoleSnowballReceipt (source : Attribution.AttributedSource) : Set where
  constructor source-role-snowball-receipt
  field
    sourceIdentityRetained : Bool
    sourceKindRetained : Bool
    formalisationRelationshipRetained : Bool
    attributionVisibilityRetained : Bool
    proofNonImportRetained : Bool
    authorityNonCreationRetained : Bool
    futureSourceRoleAxesMayBeAdded : Bool
open SourceRoleSnowballReceipt public

canonicalSourceRoleSnowballReceipt :
  (source : Attribution.AttributedSource) → SourceRoleSnowballReceipt source
canonicalSourceRoleSnowballReceipt source =
  source-role-snowball-receipt true true true true true true true

------------------------------------------------------------------------
-- A source proposition/atom may therefore be admitted only with the provenance
-- coordinates required by its consumer. DOI/title/URL are identity coordinates;
-- source kind, relationship and visibility are role coordinates. None promotes
-- the proposition into proof or downstream authority.
------------------------------------------------------------------------

data CitationCreatesProof : Set where
data CitationCreatesDomainAuthority : Set where
data SourceKindCanBeDroppedAfterProjection : Set where
data FormalisationRelationshipCanBeDroppedAfterProjection : Set where
data AttributionVisibilityCanBeDroppedAfterProjection : Set where

citationDoesNotCreateProof : CitationCreatesProof → ⊥
citationDoesNotCreateProof ()

citationDoesNotCreateAuthority : CitationCreatesDomainAuthority → ⊥
citationDoesNotCreateAuthority ()

sourceKindMustSnowballWhenRelevant : SourceKindCanBeDroppedAfterProjection → ⊥
sourceKindMustSnowballWhenRelevant ()

relationshipMustSnowballWhenRelevant : FormalisationRelationshipCanBeDroppedAfterProjection → ⊥
relationshipMustSnowballWhenRelevant ()

visibilityMustSnowballWhenRelevant : AttributionVisibilityCanBeDroppedAfterProjection → ⊥
visibilityMustSnowballWhenRelevant ()

record AttributionSnowballBoundary : Set where
  constructor attribution-snowball-boundary
  field
    attributionInstantiatesPluralLens : Bool
    attributionAndPluralLensAreIdenticalStructures : Bool
    sourceRolesMaySnowball : Bool
    citationMayPromoteProof : Bool
    citationMayCreateAuthority : Bool
open AttributionSnowballBoundary public

canonicalAttributionSnowballBoundary : AttributionSnowballBoundary
canonicalAttributionSnowballBoundary =
  attribution-snowball-boundary true false true false false
