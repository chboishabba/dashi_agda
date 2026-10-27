module DASHI.Unified.PNFDistilledNonPromotionTOEExact where

------------------------------------------------------------------------
-- Compatibility and process facade for the PNF-distilled capsule.
--
-- Mathematical and source-boundary proof authority lives in:
--
--   DASHI.Unified.PNFSourceBoundaryTOEExact
--
-- This module adds only the capsule ZKP/process receipt and the existing
-- meta-introspector attribution coordinate.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Unified.PNFSourceBoundaryTOEExact as Boundary
import DASHI.Interop.DistributedEpistemicFabricSourceAtlasExact as Fabric

------------------------------------------------------------------------
-- Compatibility aliases.
--
-- No duplicate theorem logic is defined here.
------------------------------------------------------------------------

PNFDistilledNonPromotionBoundary : Set₁
PNFDistilledNonPromotionBoundary =
  Boundary.PNFSourceBoundaryTOEReceipt

canonicalPNFDistilledNonPromotionBoundary :
  PNFDistilledNonPromotionBoundary
canonicalPNFDistilledNonPromotionBoundary =
  Boundary.canonicalPNFSourceBoundaryTOEReceipt

metaIntrospectorAttributionRule : String
metaIntrospectorAttributionRule =
  Fabric.attributionRule

------------------------------------------------------------------------
-- ZKP O/R/C/S/L/P/G/F process receipt.
--
-- This receipt is governance metadata.
-- It does not create mathematical or source authority.
------------------------------------------------------------------------

record PNFDistilledReuseZKPReceipt : Set₁ where
  constructor pnf-distilled-reuse-zkp-receipt
  field
    objectiveRefs : List String
    reuseRefs : List String
    constructionRefs : List String
    safetyInvariantRefs : List String
    laneRefs : List String
    preconditionRefs : List String
    postconditionRefs : List String
    governanceRefs : List String
    verificationRefs : List String

    sharedLexemeCreatesSemanticIdentity : Bool
    sharedLexemeCreatesSemanticIdentityIsFalse :
      sharedLexemeCreatesSemanticIdentity ≡ false

    diagnosticCheckCreatesTheoremPromotion : Bool
    diagnosticCheckCreatesTheoremPromotionIsFalse :
      diagnosticCheckCreatesTheoremPromotion ≡ false

    sourceIdentifierCreatesProofAuthority : Bool
    sourceIdentifierCreatesProofAuthorityIsFalse :
      sourceIdentifierCreatesProofAuthority ≡ false

    esdSurfaceMutationAllowed : Bool
    esdSurfaceMutationAllowedIsFalse :
      esdSurfaceMutationAllowed ≡ false

open PNFDistilledReuseZKPReceipt public

canonicalPNFDistilledReuseZKPReceipt :
  PNFDistilledReuseZKPReceipt
canonicalPNFDistilledReuseZKPReceipt =
  pnf-distilled-reuse-zkp-receipt
    ( "Normalize the PNF-distilled capsule onto the canonical PNF source boundary."
    ∷ [] )
    ( "DASHI.Unified.PNFSourceBoundaryTOEExact"
    ∷ "DASHI.Interop.DistributedEpistemicFabricSourceAtlasExact"
    ∷ [] )
    ( "Reuse the canonical PNF source-boundary receipt."
    ∷ "Add process metadata only."
    ∷ [] )
    ( "Shared words do not create semantic identity."
    ∷ "Diagnostic checks do not create theorem promotion."
    ∷ "Bibliographic identifiers do not create proof authority."
    ∷ "Meta-introspector attribution remains source attribution."
    ∷ [] )
    ( "One compatibility and governance lane."
    ∷ "ESD surfaces remain read-only."
    ∷ [] )
    ( "The canonical PNF source-boundary owner exists."
    ∷ "No lexical match is treated as a theorem join."
    ∷ [] )
    ( "The focused TOE root reaches the canonical PNF source boundary."
    ∷ "DASHI.Unifier reaches the same canonical receipt."
    ∷ "The distilled facade contains no duplicate theorem logic."
    ∷ [] )
    ( "ITIL, ISO, NIST AI RMF, Six Sigma, C4, PlantUML, and ASD-STE100 remain process or presentation lenses."
    ∷ "Original theorem owners and meta-introspector sources retain attribution."
    ∷ [] )
    ( "Run repository related, discover, and lineage checks."
    ∷ "Run structural preflight on the canonical boundary and validation."
    ∷ "Reject trust escapes."
    ∷ "Reject ESD path changes."
    ∷ "Kernel-check only on an exact-head receipt."
    ∷ [] )
    false refl
    false refl
    false refl
    false refl
