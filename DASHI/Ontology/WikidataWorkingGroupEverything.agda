module DASHI.Ontology.WikidataWorkingGroupEverything where

------------------------------------------------------------------------
-- FOCUSED WIKIDATA / JMD HANDOFF SURFACE
--
-- Keep the outward ontology package small: existing JMD theorem contracts plus
-- the BFO entity-root, query-indexed mapping, applicability, attribution, and
-- higher-order-fiction/context distinctions required by the working-group case.
------------------------------------------------------------------------

import DASHI.Ontology.LeanWikidataEverything
import DASHI.Ontology.WikidataBFOEntityScopeExact
import DASHI.Ontology.WikidataBFOMappingInferenceLatticeExact
import DASHI.Ontology.WikidataBFOApplicabilityFibreExact
import DASHI.Ontology.WikidataBFOEntityRootMappingDiagnosticExact
import DASHI.Ontology.WikidataHigherOrderFictionContextExact
import DASHI.Ontology.WikidataWorkingGroupEntityScopeRegression
