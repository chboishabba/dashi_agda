module DASHI.Ontology.WikidataWorkingGroupEverything where

------------------------------------------------------------------------
-- FOCUSED WIKIDATA / JMD HANDOFF SURFACE
--
-- The public root deliberately excludes justice/education domain applications.
-- It exposes the JMD theorem contracts, BFO/entity-scope cases, exact
-- contradiction attribution, interpretation/governance/reopening, and the
-- generic information-order machinery needed to explain the diagnostics.
------------------------------------------------------------------------

import DASHI.Ontology.LeanWikidataEverything
import DASHI.Ontology.LeanWikidataLatestEpistemicConformanceBridge

-- Existing entity-scope / higher-order class tranche.
import DASHI.Ontology.WikidataBFOEntityScopeExact
import DASHI.Ontology.WikidataBFOMappingInferenceLatticeExact
import DASHI.Ontology.WikidataBFOApplicabilityFibreExact
import DASHI.Ontology.WikidataBFOEntityRootMappingDiagnosticExact
import DASHI.Ontology.WikidataHigherOrderFictionContextExact
import DASHI.Ontology.WikidataWorkingGroupEntityScopeRegression

-- Cross-ontology attribution and exact class-algebra semantics.
import DASHI.Interop.WikidataDerivationSupportSquareExact
import DASHI.Ontology.CrossOntologyContradictionAttributionExact
import DASHI.Ontology.DisjointUnionLatticeJMDBridgeExact
import DASHI.Ontology.InferenceLanguageIndexedAlignmentSafetyExact
import DASHI.Ontology.BFOContinuantOccurrentWikidataAttributionExact
import DASHI.Ontology.RdfViewInformationOrderJMDBridgeExact

-- Alice/Finn/Brown/Kimber-inspired generic ontology instances.  The source
-- papers calibrate interpretation/governance boundaries; they are not imported
-- as proof authority or Biology dependencies.
import DASHI.Ontology.WikidataInterpretiveDiagnosticExact
import DASHI.Ontology.WikidataDiagnosticGovernanceExact
import DASHI.Ontology.WikidataRepairReopeningExact
import DASHI.Ontology.WikidataCheckerResultAttributionExact

-- Generic mathematical owners used by the outward ontology package.
import DASHI.Algebra.ClaimIndexedEvidencePolarityExact
import DASHI.Core.RequiredAxisSupportSquareExact
import DASHI.Core.ActiveObligationEvidenceFibreExact
import DASHI.Core.IndexedInterpretationMorphismExact
import DASHI.Core.ObserverRefinementLatticeExact
import DASHI.Core.ObserverIncomparabilityTypedJoinExact
import DASHI.Cognition.PNF.EditTransportLeafLocalityExact
