module DASHI.Law.SensibLawWoogarooIbrahimLandscapeGeneticsExtensionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Wikimedia.IdentifierExact as Id
import DASHI.Wikimedia.DashiKnowledgeTraversalFunnelExact as Ibrahim
import DASHI.Law.SensibLawWoogarooIbrahimDeweyQidLegalAtomExact as Canonical
import DASHI.Law.SensibLawWoogarooLegalConsumerAtomCompletionExact as Atom
import DASHI.Law.SensibLawWoogarooEvidenceDependencyMatrixExact as Dependency

------------------------------------------------------------------------
-- CANONICAL IBRAHIM EXTENSION: LANDSCAPE GENETICS / SEMIURBAN POPULATION
--
-- Extends the existing Woogaroo Ibrahim/Dewey/QID/legal-atom lane.  This file
-- does not define another traversal or source ontology.  It adds primary
-- landscape-genetics / semiurban-population sources that sharpen the first
-- unpaid s 13 population-identification bridge and the s 102 causal mechanism.
------------------------------------------------------------------------

koalaQid : Id.ItemId
koalaQid = Canonical.koalaQid

geneFlowQid : Id.ItemId
geneFlowQid = Canonical.geneFlowQid

habitatFragmentationQid : Id.ItemId
habitatFragmentationQid = Canonical.habitatFragmentationQid

populationGeneticsQid : Id.ItemId
populationGeneticsQid = Canonical.populationGeneticsQid

------------------------------------------------------------------------
-- Primary peer-reviewed source snowball.
------------------------------------------------------------------------

fowlerEtAl2000 : Source.AttributedSource
fowlerEtAl2000 = Source.mkDOISource
  "E. V. Fowler; B. A. Houlden; P. Hoeben; P. Timms"
  "Genetic diversity and gene flow among southeastern Queensland koalas (Phascolarctos cinereus)"
  "Molecular Ecology 9(2), 155-164"
  "2000"
  "10.1046/j.1365-294x.2000.00844.x"
  "https://pubmed.ncbi.nlm.nih.gov/10672159/"
  Source.academicArticleSource
  "Primary southeast-Queensland genetic study of 96 koalas from five populations. It supports treating population structure and gene flow as empirical objects rather than inferring a population from a development boundary."
  Source.publicAttribution

rhodesEtAl2006 : Source.AttributedSource
rhodesEtAl2006 = Source.mkDOISource
  "Jonathan R. Rhodes; Thorsten Wiegand; Clive A. McAlpine; John Callaghan; Daniel Lunney; Michiala Bowen; Hugh P. Possingham"
  "Modeling species' distributions to improve conservation in semiurban landscapes: koala case study"
  "Conservation Biology 20(2), 449-459"
  "2006"
  "10.1111/j.1523-1739.2006.00330.x"
  "https://pubmed.ncbi.nlm.nih.gov/16903106/"
  Source.academicArticleSource
  "Primary semiurban Koala distribution study separating natural habitat quality from anthropogenic impacts. It supplies a spatially explicit method/context for testing Springview habitat function, not a same-object Springview finding."
  Source.publicAttribution

dudaniecEtAl2013 : Source.AttributedSource
dudaniecEtAl2013 = Source.mkDOISource
  "Rachael Y. Dudaniec; Jonathan R. Rhodes; Jessica Worthington Wilmer; Mitchell Lyons; Kristen E. Lee; Clive A. McAlpine; Frank N. Carrick"
  "Using multilevel models to identify drivers of landscape-genetic structure among management areas"
  "Molecular Ecology 22(14), 3752-3765"
  "2013"
  "10.1111/mec.12359"
  "https://pubmed.ncbi.nlm.nih.gov/23730800/"
  Source.academicArticleSource
  "Primary landscape-genetics study using southeast-Queensland Koala data across management areas. It supports a management-scale route from landscape structure to gene-flow analysis."
  Source.publicAttribution

uq2014Summary : Source.AttributedSource
uq2014Summary = Source.mkNoDOISource
  "The University of Queensland"
  "Better urban planning can save koalas"
  "UQ News"
  "2014"
  "https://news.uq.edu.au/article/2014/03/better-urban-planning-can-save-koalas"
  Source.institutionalSource
  "Secondary institutional signpost to Dudaniec et al. 2013. It reports the management interpretation but is not counted as a second independent scientific producer."
  Source.publicAttribution

landscapeGeneticsExtensionAtlas : Source.AttributedSourceAtlas
landscapeGeneticsExtensionAtlas = Source.mkSourceAtlas
  "Woogaroo Ibrahim landscape-genetics source extension"
  "DASHI.Law.SensibLawWoogarooIbrahimLandscapeGeneticsExtensionExact"
  (fowlerEtAl2000 ∷ rhodesEtAl2006 ∷ dudaniecEtAl2013 ∷ uq2014Summary ∷ [])
  "Three primary peer-reviewed empirical/method sources plus one secondary UQ signpost. DOI identity is source identity only; regional science remains distinct from same-object Springview evidence and legal conclusion."

------------------------------------------------------------------------
-- Canonical Ibrahim coordinates.  Dewey/QID are navigation metadata, not
-- proof or authority.  Paper-level QIDs are left unresolved rather than
-- manufactured; stable concept QIDs are reused from the canonical owner.
------------------------------------------------------------------------

fowlerGeneticsCoordinate : Ibrahim.DashiKnowledgeCoordinate
fowlerGeneticsCoordinate = Ibrahim.dashi-knowledge-coordinate
  "DASHI/Law/SensibLawWoogarooIbrahimLandscapeGeneticsExtensionExact.agda"
  "southeast-Queensland Koala genetic diversity and gene flow"
  Canonical.populationGeneticsDewey
  (Id.rawItemId populationGeneticsQid)
  "doi:10.1046/j.1365-294x.2000.00844.x; paper QID unresolved"

rhodesSemiurbanCoordinate : Ibrahim.DashiKnowledgeCoordinate
rhodesSemiurbanCoordinate = Ibrahim.dashi-knowledge-coordinate
  "DASHI/Law/SensibLawWoogarooIbrahimLandscapeGeneticsExtensionExact.agda"
  "semiurban Koala distribution / natural habitat versus anthropogenic impacts"
  Canonical.conservationDewey
  (Id.rawItemId koalaQid)
  "doi:10.1111/j.1523-1739.2006.00330.x; paper QID unresolved"

dudaniecLandscapeGeneticsCoordinate : Ibrahim.DashiKnowledgeCoordinate
dudaniecLandscapeGeneticsCoordinate = Ibrahim.dashi-knowledge-coordinate
  "DASHI/Law/SensibLawWoogarooIbrahimLandscapeGeneticsExtensionExact.agda"
  "Koala landscape-genetic structure among management areas"
  Canonical.populationGeneticsDewey
  (Id.rawItemId geneFlowQid)
  "doi:10.1111/mec.12359; paper QID unresolved"

------------------------------------------------------------------------
-- Cross-pollination into the existing legal consumers.
------------------------------------------------------------------------

fowlerSupportsPopulationIdentityMethod : Ibrahim.DashiFirstLinkEdge
fowlerSupportsPopulationIdentityMethod = Ibrahim.dashi-first-link-edge
  fowlerGeneticsCoordinate Canonical.s13EssentialityCoordinate Ibrahim.crossPollinatesWith
  Ibrahim.canonicalDashiFirstLinkPolicy
  "Regional genetic heterogeneity shows that viable-population identity is an empirical population question. It does not identify the current Springview population."
  true

rhodesSupportsS102Mechanism : Ibrahim.DashiFirstLinkEdge
rhodesSupportsS102Mechanism = Ibrahim.dashi-first-link-edge
  rhodesSemiurbanCoordinate Canonical.s102StatutoryCoordinate Ibrahim.supportedBy
  Ibrahim.canonicalDashiFirstLinkPolicy
  "Semiurban distribution modelling supports separation of natural habitat quality from anthropogenic effects when forming an expert s 102 opinion. It remains method/context only."
  true

dudaniecSupportsPopulationConnectivityMethod : Ibrahim.DashiFirstLinkEdge
dudaniecSupportsPopulationConnectivityMethod = Ibrahim.dashi-first-link-edge
  dudaniecLandscapeGeneticsCoordinate Canonical.s13EssentialityCoordinate Ibrahim.crossPollinatesWith
  Ibrahim.canonicalDashiFirstLinkPolicy
  "Management-scale landscape genetics gives a concrete route to define population connectivity beyond a development boundary. It does not pay the local same-object population join."
  true

------------------------------------------------------------------------
-- Legal atom bindings reuse the canonical atom carrier.
------------------------------------------------------------------------

fowlerToS13Essentiality : Canonical.KnowledgeAtomBinding
fowlerToS13Essentiality = Canonical.knowledge-atom-binding
  fowlerGeneticsCoordinate Atom.habitatPopulationEssentialityAtom Atom.nca13EssentialityConsumer
  Canonical.regionalComparatorScience Canonical.sameRegionNotSameObject true false
  "Independent historical regional genetics supports the form of the population question but does not identify the current viable Springview/Opossum-Woogaroo population."

rhodesToS102Effect : Canonical.KnowledgeAtomBinding
rhodesToS102Effect = Canonical.knowledge-atom-binding
  rhodesSemiurbanCoordinate Atom.likelySignificantDetrimentalEffectAtom Atom.nca102InterimOrderConsumer
  Canonical.peerReviewedMechanism Canonical.sameRegionNotSameObject true false
  "Semiurban natural-versus-anthropogenic modelling is admissible mechanism/method context; it does not establish likely significant detrimental effect for 9281."

dudaniecToS13Essentiality : Canonical.KnowledgeAtomBinding
dudaniecToS13Essentiality = Canonical.knowledge-atom-binding
  dudaniecLandscapeGeneticsCoordinate Atom.habitatPopulationEssentialityAtom Atom.nca13EssentialityConsumer
  Canonical.regionalComparatorScience Canonical.sameRegionNotSameObject true false
  "Landscape-genetic structure supports an empirically defined population/connectivity analysis. Same-object population identity and essentiality remain unpaid."

------------------------------------------------------------------------
-- Dependency/payment state: more literature improves method calibration but
-- does not pay the two live local residuals.
------------------------------------------------------------------------

record LandscapeGeneticsExtensionState : Set where
  constructor landscape-genetics-extension-state
  field
    primaryDoiSourcesAdded : Nat
    secondarySignpostsAdded : Nat
    conceptQidsReused : Nat
    paperQidsResolved : Nat
    regionalGeneticEvidencePaid : Bool
    semiurbanMethodEvidencePaid : Bool
    localPopulationIdentityPaid : Bool
    localCurrentEffectOpinionPaid : Bool
    firstUnpaidS102 : String
    firstUnpaidS13 : String

currentLandscapeGeneticsExtensionState : LandscapeGeneticsExtensionState
currentLandscapeGeneticsExtensionState = landscape-genetics-extension-state
  3 1 4 0 true true false false
  "Independent current ecological opinion applying the actual Queensland s 12/s 102 wording to the exact 9281 process/current ecological state, explicitly testing mitigation, fragmentation, duration, reversibility and execution status."
  "Independent identification of the biologically relevant viable Koala population/community, then the without-site/severance counterfactual for persistence, movement, breeding/dispersal, gene flow and resource access."

s102DependencyState : Dependency.ConsumerDependencyState
s102DependencyState = Dependency.s102DependencyState

s13DependencyState : Dependency.ConsumerDependencyState
s13DependencyState = Dependency.s13DependencyState

------------------------------------------------------------------------
-- Ibrahim / attribution boundaries.
------------------------------------------------------------------------

data PaperDOIEqualsSameObjectEvidence : Set where
data PaperQidMissingEqualsSourceMissing : Set where
data UQSummaryEqualsIndependentPrimaryStudy : Set where
data RegionalGeneFlowEqualsLocalViablePopulation : Set where
data ThirtyPercentForestRuleEqualsSpringviewThreshold : Set where
data LiteratureCountEqualsIndependentLocalCorroboration : Set where

paperDoiDoesNotCreateSameObjectEvidence : PaperDOIEqualsSameObjectEvidence → ⊥
paperDoiDoesNotCreateSameObjectEvidence ()

missingPaperQidDoesNotEraseSource : PaperQidMissingEqualsSourceMissing → ⊥
missingPaperQidDoesNotEraseSource ()

uqSummaryDoesNotCreateIndependentPrimaryStudy : UQSummaryEqualsIndependentPrimaryStudy → ⊥
uqSummaryDoesNotCreateIndependentPrimaryStudy ()

regionalGeneFlowDoesNotIdentifyLocalPopulation : RegionalGeneFlowEqualsLocalViablePopulation → ⊥
regionalGeneFlowDoesNotIdentifyLocalPopulation ()

thirtyPercentRuleDoesNotBecomeSiteThreshold : ThirtyPercentForestRuleEqualsSpringviewThreshold → ⊥
thirtyPercentRuleDoesNotBecomeSiteThreshold ()

literatureMultiplicityDoesNotCreateLocalCorroboration : LiteratureCountEqualsIndependentLocalCorroboration → ⊥
literatureMultiplicityDoesNotCreateLocalCorroboration ()
