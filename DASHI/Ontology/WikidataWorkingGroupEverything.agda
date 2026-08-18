module DASHI.Ontology.WikidataWorkingGroupEverything where

------------------------------------------------------------------------
-- FOCUSED WIKIDATA / JMD HANDOFF SURFACE
--
-- Keep the outward ontology package small: existing JMD theorem contracts plus
-- the new BFO entity-root and higher-order-fiction/context distinctions.
------------------------------------------------------------------------

import DASHI.Ontology.LeanWikidataEverything
import DASHI.Ontology.WikidataBFOEntityScopeExact
import DASHI.Ontology.WikidataHigherOrderFictionContextExact
import DASHI.Ontology.WikidataWorkingGroupEntityScopeRegression
