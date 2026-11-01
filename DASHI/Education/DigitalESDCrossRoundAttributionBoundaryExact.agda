module DASHI.Education.DigitalESDCrossRoundAttributionBoundaryExact where

import DASHI.Core.SnowballAttributionProvenanceInvariantExact as Snowball

-- Thin canonical pin only. No digital-ESD-specific attribution policy is
-- introduced here: previous and future rounds reuse the repository's existing
-- source-role/proof/authority snowball invariant unchanged.

crossRoundAttributionBoundary : Snowball.AttributionSnowballBoundary
crossRoundAttributionBoundary = Snowball.canonicalAttributionSnowballBoundary
