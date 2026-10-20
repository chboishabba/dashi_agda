module DASHI.Wikimedia.BH4ProteinWikimediaEverything where

-- Focused Wikimedia root for the BH4/UniProt identity cross-pollination.
-- Reuses the existing external-identity policy and keeps acquisition/regression
-- isolated from the broad Wikimedia.Everything import fanout.

import DASHI.Wikimedia.SnowballExternalIdentityAvailabilityExact
import DASHI.Wikimedia.PredicateNormalFormWikipediaQidBridgeExact
import DASHI.Wikimedia.BH4ProteinWikimediaIdentityExact
import DASHI.Wikimedia.BH4ProteinWikimediaIdentityRegression
