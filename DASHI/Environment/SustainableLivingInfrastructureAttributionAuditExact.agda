module DASHI.Environment.SustainableLivingInfrastructureAttributionAuditExact where

open import DASHI.Core.Prelude

import DASHI.Core.ScientificWorkAttributionExact as Attribution
import DASHI.Environment.SustainableAgricultureManagementSourceRegistryExact as SustainableSources
import DASHI.Environment.SustainableAgricultureCanonicalAttributionBridgeExact as SustainableBridge
import DASHI.Environment.KNFSourceAttributionLineageExact as KNF
import DASHI.Environment.PluralSustainableLandManagementTraditionsExact as Traditions
import DASHI.Environment.NaturalBiologicalCompostInterventionAtlasExact as NaturalAtlas
import DASHI.Environment.AquaticLivingInfrastructureSourceRegistryExact as AquaticSources
import DASHI.Physics.Plasma.PlasmaActivatedWaterAgricultureSourceRegistryExact as PAWSources
import DASHI.Biology.Agriculture.HungriaBiologicalNitrogenFixationSourceAtlas as LegacyBNF
import DASHI.Environment.NitrogenPathwaySourceRegistryExact as NitrogenSources

------------------------------------------------------------------------
-- FOCUSED ATTRIBUTION AUDIT FOR TODAY'S SUSTAINABLE / LIVING-INFRASTRUCTURE
-- TRANCHE.
--
-- This is a validation owner, not another provenance architecture.  It asks
-- whether source-bearing objects can be projected onto the canonical
-- ScientificWorkAttributionExact.ClaimOwner distinction without laundering a
-- DASHI reconstruction or inference back into an external source.
------------------------------------------------------------------------

data AttributionCoverage : Set where
  canonicalOwnerEmbedded
  canonicalStageOwnerWelded
  canonicalExternalEntitlementWelded
  legacyAtlasRequiresExplicitAdapter : AttributionCoverage

record LegacyBNFExternalEntitlement
    (source : LegacyBNF.BNFSource) : Set where
  constructor legacy-bnf-external-entitlement
  field
    owner : Attribution.ClaimOwner
    ownerIsExternal : owner ≡ Attribution.externalSourceOwner
    scopeReference : String

open LegacyBNFExternalEntitlement public

entitleLegacyBNFSource :
  (source : LegacyBNF.BNFSource) → LegacyBNFExternalEntitlement source
entitleLegacyBNFSource source =
  legacy-bnf-external-entitlement
    Attribution.externalSourceOwner
    refl
    "Entitlement covers only the bounded external BNF source reading retained by the legacy atlas; DASHI carrier design and cross-pathway inference remain DASHI-owned."

------------------------------------------------------------------------
-- Executable spot checks on the owners introduced/reused today.
------------------------------------------------------------------------

knfPracticeOwnerIsExternal :
  KNF.claimOwner KNF.choKoyamaPracticeLineage ≡ Attribution.externalSourceOwner
knfPracticeOwnerIsExternal = refl

knfCrossSourceBridgeOwnerIsDashiInference :
  KNF.claimOwner KNF.knfPermacultureCrossSourceBridge ≡ Attribution.dashiInferenceOwner
knfCrossSourceBridgeOwnerIsDashiInference = refl

sustainableExternalStageOwnerIsExternal :
  SustainableBridge.canonicalOwnerForStage SustainableSources.externalSourceClaim
  ≡ Attribution.externalSourceOwner
sustainableExternalStageOwnerIsExternal = refl

sustainableReconstructionOwnerIsDashiFormalisation :
  SustainableBridge.canonicalOwnerForStage SustainableSources.dashiReconstruction
  ≡ Attribution.dashiFormalisationOwner
sustainableReconstructionOwnerIsDashiFormalisation = refl

sustainableCrossSourceOwnerIsDashiInference :
  SustainableBridge.canonicalOwnerForStage SustainableSources.dashiCrossSourceInference
  ≡ Attribution.dashiInferenceOwner
sustainableCrossSourceOwnerIsDashiInference = refl

naturalAtlasBerkeleyStageResolvesExternal :
  SustainableBridge.canonicalOwnerForStage
    (NaturalAtlas.sourceStage NaturalAtlas.berkeleyRapidCompostIdentity)
  ≡ Attribution.externalSourceOwner
naturalAtlasBerkeleyStageResolvesExternal = refl

aquaticReviewOwnerIsExternal :
  AquaticSources.claimOwner AquaticSources.aquaponicsCriticalReview2025
  ≡ Attribution.externalSourceOwner
aquaticReviewOwnerIsExternal = refl

pawReviewOwnerIsExternal :
  PAWSources.claimOwner PAWSources.robinsonStapelmann2024
  ≡ Attribution.externalSourceOwner
pawReviewOwnerIsExternal = refl

nitrogenHaberBoschOwnerIsExternal :
  NitrogenSources.claimOwner NitrogenSources.haberBoschReview2024
  ≡ Attribution.externalSourceOwner
nitrogenHaberBoschOwnerIsExternal = refl

nitrogenKNFRecyclingOwnerIsDashiInference :
  NitrogenSources.claimOwner NitrogenSources.knfLocalRecyclingLineage
  ≡ Attribution.dashiInferenceOwner
nitrogenKNFRecyclingOwnerIsDashiInference = refl

------------------------------------------------------------------------
-- Tradition sources are external source carriers, but their records predate an
-- embedded canonical ClaimOwner.  Use the explicit bridge instead of assuming
-- that every statement in the importing module belongs to the tradition.
------------------------------------------------------------------------

syntropicExternalEntitlement :
  SustainableBridge.TraditionSourceExternalEntitlement Traditions.syntropicGotsch
syntropicExternalEntitlement =
  SustainableBridge.entitleTraditionSource Traditions.syntropicGotsch

------------------------------------------------------------------------
-- Audit result.
------------------------------------------------------------------------

record TodayAttributionAudit : Set where
  constructor today-attribution-audit
  field
    knfHasCanonicalStageOwnerConsistency : Bool
    sustainableClaimStageNowHasCanonicalOwnerWeld : Bool
    pluralTraditionSourcesHaveExplicitExternalEntitlement : Bool
    naturalInterventionAtlasStageCanResolveCanonicalOwner : Bool
    aquaticSourcesEmbedCanonicalOwner : Bool
    pawSourcesEmbedCanonicalOwner : Bool
    nitrogenComparisonSourcesCarryCanonicalOwner : Bool
    legacyBNFNeedsExplicitAdapterBecauseOwnerNotEmbedded : Bool
    dashiCrossSourceInferenceMayBeAttributedToExternalSource : Bool
    sourceLocatorStringAloneMayPayExternalAuthority : Bool

canonicalTodayAttributionAudit : TodayAttributionAudit
canonicalTodayAttributionAudit =
  today-attribution-audit
    true true true true true true true true false false

------------------------------------------------------------------------
-- WrongType boundaries found by the audit.
------------------------------------------------------------------------

data LocatorStringMeansSourceAuthorityPermission : Set where
data ExternalPracticeSourceMeansDashiBridgeAuthorshipPermission : Set where
data LegacyAtlasCommentMeansCanonicalTypedOwnerPermission : Set where

locatorStringDoesNotPayAuthority : LocatorStringMeansSourceAuthorityPermission → ⊥
locatorStringDoesNotPayAuthority ()

externalPracticeSourceDoesNotOwnDashiBridge :
  ExternalPracticeSourceMeansDashiBridgeAuthorshipPermission → ⊥
externalPracticeSourceDoesNotOwnDashiBridge ()

legacyCommentDoesNotDefinitionallyProvideTypedOwner :
  LegacyAtlasCommentMeansCanonicalTypedOwnerPermission → ⊥
legacyCommentDoesNotDefinitionallyProvideTypedOwner ()
