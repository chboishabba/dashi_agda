module DASHI.Environment.SustainableAgricultureCanonicalAttributionBridgeExact where

open import DASHI.Core.Prelude

import DASHI.Core.ScientificWorkAttributionExact as Attribution
import DASHI.Environment.SustainableAgricultureManagementSourceRegistryExact as Sources
import DASHI.Environment.PluralSustainableLandManagementTraditionsExact as Traditions

------------------------------------------------------------------------
-- CANONICAL ATTRIBUTION WELD FOR SUSTAINABLE-AGRICULTURE CLAIM STAGES
--
-- The sustainable-agriculture registry predates a direct type-level weld from
-- its ClaimStage to ScientificWorkAttributionExact.ClaimOwner.  This module
-- closes that gap without replacing either owner.
------------------------------------------------------------------------

canonicalOwnerForStage : Sources.ClaimStage → Attribution.ClaimOwner
canonicalOwnerForStage Sources.externalSourceClaim = Attribution.externalSourceOwner
canonicalOwnerForStage Sources.dashiReconstruction = Attribution.dashiFormalisationOwner
canonicalOwnerForStage Sources.dashiCrossSourceInference = Attribution.dashiInferenceOwner
canonicalOwnerForStage Sources.dashiTheorem = Attribution.dashiInferenceOwner
canonicalOwnerForStage Sources.promotedRecommendation = Attribution.unresolvedClaimOwner

record CanonicalStageOwnerReceipt (stage : Sources.ClaimStage) : Set where
  constructor canonical-stage-owner-receipt
  field
    owner : Attribution.ClaimOwner
    ownerMatchesCanonicalStage : owner ≡ canonicalOwnerForStage stage

open CanonicalStageOwnerReceipt public

canonicalStageOwnerReceipt : (stage : Sources.ClaimStage) → CanonicalStageOwnerReceipt stage
canonicalStageOwnerReceipt stage = canonical-stage-owner-receipt (canonicalOwnerForStage stage) refl

------------------------------------------------------------------------
-- External source records without an embedded ClaimOwner are admitted only
-- through an explicit external-source entitlement.  The entitlement covers
-- the bounded source reading; it does not own DASHI reconstructions.
------------------------------------------------------------------------

record SustainableSourceExternalEntitlement
    (source : Sources.SustainableAgricultureSource) : Set where
  constructor sustainable-source-external-entitlement
  field
    owner : Attribution.ClaimOwner
    ownerIsExternal : owner ≡ Attribution.externalSourceOwner

open SustainableSourceExternalEntitlement public

entitleSustainableSource :
  (source : Sources.SustainableAgricultureSource) →
  SustainableSourceExternalEntitlement source
entitleSustainableSource source =
  sustainable-source-external-entitlement Attribution.externalSourceOwner refl

record TraditionSourceExternalEntitlement
    (source : Traditions.TraditionSource) : Set where
  constructor tradition-source-external-entitlement
  field
    owner : Attribution.ClaimOwner
    ownerIsExternal : owner ≡ Attribution.externalSourceOwner

open TraditionSourceExternalEntitlement public

entitleTraditionSource :
  (source : Traditions.TraditionSource) →
  TraditionSourceExternalEntitlement source
entitleTraditionSource source =
  tradition-source-external-entitlement Attribution.externalSourceOwner refl

------------------------------------------------------------------------
-- Non-laundering barriers.
------------------------------------------------------------------------

data ExternalSourceEntitlementMeansDashiInferenceOwnershipPermission : Set where
data DashiReconstructionMeansExternalAuthorshipPermission : Set where
data PromotionStageMeansExternalSourceTruthPermission : Set where

externalEntitlementDoesNotOwnDashiInference :
  ExternalSourceEntitlementMeansDashiInferenceOwnershipPermission → ⊥
externalEntitlementDoesNotOwnDashiInference ()

dashiReconstructionDoesNotTransferExternalAuthorship :
  DashiReconstructionMeansExternalAuthorshipPermission → ⊥
dashiReconstructionDoesNotTransferExternalAuthorship ()

promotionStageDoesNotBecomeExternalSourceTruth :
  PromotionStageMeansExternalSourceTruthPermission → ⊥
promotionStageDoesNotBecomeExternalSourceTruth ()
