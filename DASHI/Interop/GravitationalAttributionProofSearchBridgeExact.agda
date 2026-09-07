module DASHI.Interop.GravitationalAttributionProofSearchBridgeExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)

import DASHI.Physics.GR.GravitationalEpistemicLineageExact as Lineage
import DASHI.Law.SensibLawProofDirectedSearchIntentExact as Search

------------------------------------------------------------------------
-- GRAVITATIONAL ATTRIBUTION RESIDUAL -> EXISTING PRODUCER CLASS
--
-- Missing provenance is scheduled using the existing proof-search vocabulary.
-- The bridge does not fabricate metadata and retrieval does not pay the
-- underlying physical claim merely by finding a document.
------------------------------------------------------------------------

producerForAttributionResidual :
  Lineage.GravitationalAttributionResidual → Search.ProducerClass
producerForAttributionResidual Lineage.missingAuthorOrResponsibleBody =
  Search.attributionProducer
producerForAttributionResidual Lineage.missingTitle =
  Search.attributionProducer
producerForAttributionResidual Lineage.missingStableIdentifier =
  Search.identityProducer
producerForAttributionResidual Lineage.missingCarrierLocation =
  Search.propositionSourceProducer
producerForAttributionResidual Lineage.missingInspectionDate =
  Search.temporalProducer
producerForAttributionResidual Lineage.missingExactClaimScope =
  Search.discriminatorProducer
producerForAttributionResidual Lineage.carrierNotInspectedForClaim =
  Search.propositionSourceProducer
producerForAttributionResidual Lineage.missingInternalModulePath =
  Search.identityProducer
producerForAttributionResidual Lineage.missingInternalTheoremName =
  Search.identityProducer
producerForAttributionResidual Lineage.missingRepositoryRevision =
  Search.temporalProducer
producerForAttributionResidual Lineage.missingProofStatementScope =
  Search.discriminatorProducer

record GravitationalAttributionProofSearchBoundary : Set where
  constructor gravitational-attribution-proof-search-boundary
  field
    missingAttributionSchedulesExistingProducer : Bool
    missingMetadataMayBeSynthesisedByBridge : Bool
    retrievedSourceAutomaticallyPaysPhysicalClaim : Bool
    internalProofLineageRequiresExternalBibliographyProducer : Bool

canonicalGravitationalAttributionProofSearchBoundary :
  GravitationalAttributionProofSearchBoundary
canonicalGravitationalAttributionProofSearchBoundary =
  gravitational-attribution-proof-search-boundary true false false false

stableIdentifierRouteExact :
  producerForAttributionResidual Lineage.missingStableIdentifier
    ≡ Search.identityProducer
stableIdentifierRouteExact = refl

claimScopeRouteExact :
  producerForAttributionResidual Lineage.missingExactClaimScope
    ≡ Search.discriminatorProducer
claimScopeRouteExact = refl
