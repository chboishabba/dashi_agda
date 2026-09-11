module DASHI.Law.SensibLawWoogarooIbrahimSnowballLegalAtomAtlasExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Wikimedia.IdentifierExact as Identifier
import DASHI.Law.SensibLawWoogarooLegalConsumerAtomCompletionExact as Atom
import DASHI.Law.SensibLawWoogarooEvidenceDependencyMatrixExact as Dependency

------------------------------------------------------------------------
-- IBRAHIM-STYLE SNOWBALL FOR THE LIVE WOOGAROO LEGAL CONSUMERS
--
-- Acquisition may move outward through DOI/QID/Dewey/entity coordinates, but
-- payment remains consumer-specific.  Identifiers are navigation/provenance
-- coordinates: DOI != truth; QID != proposition semantics; Dewey != authority.
------------------------------------------------------------------------

data EvidenceRole : Set where
  primaryStatute
  primaryGovernmentStatus
  primaryEmpiricalArticle
  primaryDataset
  systematicReview
  methodsOrComparator : EvidenceRole

data PaymentRelation : Set where
  paysInput
  supportsAcquisition
  supportsCounterfactual
  supportsCalibration
  doesNotPayConsumer : PaymentRelation

record IbrahimCoordinate : Set where
  constructor ibrahim-coordinate
  field
    label : String
    dewey : String
    qid : Identifier.ItemId
    doi : String
    role : EvidenceRole
    sourceIsPrimaryForClaim : Bool
    claimScope : String

open IbrahimCoordinate public

koalaCoordinate : IbrahimCoordinate
koalaCoordinate = ibrahim-coordinate
  "Koala / Phascolarctos cinereus"
  "599.2 — mammals/marsupials working Dewey coordinate"
  (Identifier.itemId "Q36101")
  "10.48580/DFPX"
  primaryGovernmentStatus
  false
  "Entity/taxon navigation only. The Wikidata/taxonomic DOI coordinate does not establish Queensland conservation status, project occurrence, population identity or legal significance."

ecologicalConnectivityCoordinate : IbrahimCoordinate
ecologicalConnectivityCoordinate = ibrahim-coordinate
  "ecological connectivity"
  "577.0 — ecology working Dewey coordinate"
  (Identifier.itemId "Q2993449")
  "unresolvedDOI"
  methodsOrComparator
  false
  "Concept navigation for landscape movement/connectivity; not a project-specific factual claim."

habitatFragmentationCoordinate : IbrahimCoordinate
habitatFragmentationCoordinate = ibrahim-coordinate
  "habitat fragmentation"
  "577.0 — ecology working Dewey coordinate"
  (Identifier.itemId "Q913302")
  "unresolvedDOI"
  methodsOrComparator
  false
  "Concept navigation for fragmentation effects; not a causal finding for Springview."

southEastQueenslandCoordinate : IbrahimCoordinate
southEastQueenslandCoordinate = ibrahim-coordinate
  "South East Queensland"
  "919.43 — Queensland regional geography working coordinate"
  (Identifier.itemId "Q1894392")
  "unresolvedDOI"
  methodsOrComparator
  false
  "Regional navigation only; same region does not imply same population, habitat or project."

------------------------------------------------------------------------
-- Attributed scientific/government source snowball.
------------------------------------------------------------------------

dudaniec2013 : Source.AttributedSource
dudaniec2013 = Source.mkDOISource
  "Rachael Y. Dudaniec; Jonathan R. Rhodes; Jessica Worthington Wilmer; Mitchell Lyons; Kristen E. Lee; Clive A. McAlpine; Frank N. Carrick"
  "Using multilevel models to identify drivers of landscape-genetic structure among management areas"
  "Molecular Ecology 22(14):3752-3765"
  "2013"
  "10.1111/mec.12359"
  "https://doi.org/10.1111/mec.12359"
  Source.academicArticleSource
  "Primary empirical landscape-genetics study in South East Queensland. Used to snowball from generic connectivity to measurable gene-flow/population-structure questions; not used as a direct Springview population finding."
  Source.publicAttribution

lee2010 : Source.AttributedSource
lee2010 = Source.mkDOISource
  "Kristen E. Lee; Jennifer M. Seddon; Sean W. Corley; William A. H. Ellis; Stephen D. Johnston; Deidre L. de Villiers; Harriet J. Preece; Frank N. Carrick"
  "Genetic variation and structuring in the threatened koala populations of Southeast Queensland"
  "Conservation Genetics 11:2091-2103"
  "2010"
  "10.1007/s10592-009-9987-9"
  "https://doi.org/10.1007/s10592-009-9987-9"
  Source.academicArticleSource
  "Primary empirical population-genetics source. Supports acquisition of a biologically defensible viable-population unit and barrier/gene-flow evidence; does not identify the present Springview population automatically."
  Source.publicAttribution

rhodesOffset2024 : Source.AttributedSource
rhodesOffset2024 = Source.mkDOISource
  "Jonathan R. Rhodes et al."
  "Performance of habitat offsets for species conservation in dynamic human-modified landscapes"
  "People and Nature"
  "2024"
  "10.1002/pan3.10494"
  "https://doi.org/10.1002/pan3.10494"
  Source.academicArticleSource
  "Primary modelling study applying an integrated spatial land-use, koala-abundance and offset-regulation model in South East Queensland. Supports offset/additionality and dynamic-landscape counterfactual design, not a finding that the proposed 2019/8575 offsets are adequate or inadequate."
  Source.publicAttribution

seqOffsetDataset2023 : Source.AttributedSource
seqOffsetDataset2023 = Source.mkDOISource
  "Jonathan R. Rhodes; Yan Liu; Agung Wahyudi; Martine Maron; Md Sayed Iftekhar; Shantala Brisbane"
  "South East Queensland Koala Offset Analysis"
  "The University of Queensland Research Data"
  "2023"
  "10.48610/1c1164e"
  "https://doi.org/10.48610/1c1164e"
  (Source.namedSourceKind "research dataset")
  "Primary data package for the integrated South East Queensland koala offset analysis. Candidate implementation/calibration input for later LES/spatial work; not a project-specific legal conclusion."
  Source.publicAttribution

brunton2026 : Source.AttributedSource
brunton2026 = Source.mkDOISource
  "Brunton et al.; corresponding author Romane H. Cristescu"
  "Mapping connectivity for conservation of a threatened iconic mammal, the koala: Trends, challenges and opportunities"
  "Ecological Solutions and Evidence"
  "2026"
  "10.1002/2688-8319.70253"
  "https://doi.org/10.1002/2688-8319.70253"
  Source.academicArticleSource
  "Systematic-review source for current koala-connectivity methods and evidence gaps. Used to snowball contemporary method choices; secondary synthesis, not independent Springview observation."
  Source.publicAttribution

ncaSource : Source.AttributedSource
ncaSource = Source.mkNoDOISource
  "Queensland Parliamentary Counsel"
  "Nature Conservation Act 1992 — sections 12, 13, 102-105"
  "Queensland Legislation"
  "2026"
  "https://www.legislation.qld.gov.au/view/whole/html/current/act-1992-020"
  Source.governmentSource
  "Primary legal source for threatening process, critical habitat, interim conservation orders and their duration. Scientific sources can inform facts relevant to these consumers but cannot substitute for the statutory text."
  Source.publicAttribution

koalaStatusSource : Source.AttributedSource
koalaStatusSource = Source.mkNoDOISource
  "Queensland Government"
  "Changes made to wildlife categories on 8 April 2022"
  "Queensland threatened-species conservation status"
  "2022"
  "https://www.qld.gov.au/environment/plants-animals/conservation/threatened-species/classes/conservation-status/changes-categories-april-2022"
  Source.governmentSource
  "Primary government status source for the Queensland Endangered listing proposition only."
  Source.publicAttribution

woogarooIbrahimSourceAtlas : Source.AttributedSourceAtlas
woogarooIbrahimSourceAtlas = Source.mkSourceAtlas
  "Woogaroo Ibrahim-style legal/ecology snowball atlas"
  "DASHI.Law.SensibLawWoogarooIbrahimSnowballLegalAtomAtlasExact"
  (ncaSource ∷ koalaStatusSource ∷ dudaniec2013 ∷ lee2010 ∷ rhodesOffset2024 ∷ seqOffsetDataset2023 ∷ brunton2026 ∷ [])
  "Primary law and government status are separated from primary empirical ecology, primary data and secondary synthesis. DOI/QID/Dewey coordinates support navigation and acquisition only; they do not pay the live legal consumer without a same-object proposition."

------------------------------------------------------------------------
-- Intersect the Snowball with the existing legal atom machinery.
------------------------------------------------------------------------

record SourceAtomEdge : Set where
  constructor source-atom-edge
  field
    sourceLabel : String
    atom : Atom.LegalExecutionAtom
    relation : PaymentRelation
    exactUse : String
    remainingBoundary : String

open SourceAtomEdge public

statusToS102 : SourceAtomEdge
statusToS102 = source-atom-edge
  "Queensland Koala endangered-status source"
  Atom.affectedWildlifeHabitatAtom
  paysInput
  "Pays threatened-wildlife/status context for the direct s 102 route."
  "Status does not pay project exposure, threatening process, likelihood or significance of effect."

landscapeGeneticsToS13 : SourceAtomEdge
landscapeGeneticsToS13 = source-atom-edge
  "Dudaniec 2013 + Lee 2010"
  Atom.habitatPopulationEssentialityAtom
  supportsAcquisition
  "Constrains how a viable-population identity and connectivity/barrier analysis could be built independently of the development boundary."
  "Regional genetic structure does not identify the exact current Springview population and does not prove statutory essentiality."

connectivityReviewToS13 : SourceAtomEdge
connectivityReviewToS13 = source-atom-edge
  "Brunton et al. 2026 systematic review"
  Atom.habitatPopulationEssentialityAtom
  supportsCalibration
  "Provides current connectivity-mapping methods and known methodological limits for selecting an expert analysis."
  "A systematic review is method evidence, not project-specific population evidence."

offsetModelToFederal : SourceAtomEdge
offsetModelToFederal = source-atom-edge
  "Rhodes et al. 2024 + UQ 2023 offset dataset"
  Atom.offsetBaselineRiskOfLossAtom
  supportsCounterfactual
  "Supports explicit modelling of land-use change, koala abundance, offset-site availability and baseline/counterfactual outcomes."
  "The model and dataset do not establish the identity, protection status, additionality or adequacy of the proposed 2019/8575 offset parcels."

offsetModelToMaturity : SourceAtomEdge
offsetModelToMaturity = source-atom-edge
  "Rhodes et al. 2024 + UQ 2023 offset dataset"
  Atom.offsetRestorationLagAtom
  supportsCounterfactual
  "Supports separating immediate impact from delayed restoration/offset outcomes in a dynamic landscape."
  "Generic model structure does not pay project-specific restoration lag or functional equivalence."

------------------------------------------------------------------------
-- Ibrahim-style acquisition frontier: navigate outward, pay inward.
------------------------------------------------------------------------

record SnowballFrontier : Set where
  constructor snowball-frontier
  field
    consumer : String
    firstMissingSameObject : String
    preferredNextSourceClass : String
    doiQidDeweyNavigationReady : Bool
    externalLiteratureAloneCanCloseConsumer : Bool

s102Frontier : SnowballFrontier
s102Frontier = snowball-frontier
  "NCA s 102 likely significant detrimental effect"
  "Independent current ecological opinion applying ss 12/102 to the exact approved process and current habitat/wildlife state."
  "Current field/ecology expert evidence, then literature used to calibrate methods and causal expectations."
  true false

s13Frontier : SnowballFrontier
s13Frontier = snowball-frontier
  "NCA s 13 essentiality"
  "Independent identification of the biologically relevant viable Koala population/community and the Springview habitat's contribution to its persistence/connectivity."
  "Population genetics/connectivity evidence or defensible current population study tied spatially to Springview/Woogaroo."
  true false

offsetFrontier : SnowballFrontier
offsetFrontier = snowball-frontier
  "EPBC offset/additionality counterfactual"
  "Exact final offset parcel identities, existing protection/obligations, condition/maturity and without-offset risk of loss."
  "Primary parcel, covenant, offset-register, vegetation-condition and land-use evidence; UQ model used after identity is paid."
  true false

------------------------------------------------------------------------
-- Independence accounting remains inherited from the legal DAG.
------------------------------------------------------------------------

dependencyState : Dependency.ConsumerDependencyState
dependencyState = Dependency.s102DependencyState

------------------------------------------------------------------------
-- No-promotion / WrongType boundaries.
------------------------------------------------------------------------

data DOIEqualsEvidencePayment : Set where
data QIDEqualsLegalAtom : Set where
data DeweyEqualsAuthority : Set where
data RegionalStudyEqualsSpringviewPopulation : Set where
data ReviewEqualsIndependentObservation : Set where
data OffsetModelEqualsOffsetAdequacy : Set where
data MultipleCitationsEqualsIndependentCarriers : Set where

doiDoesNotPayAtom : DOIEqualsEvidencePayment → ⊥
doiDoesNotPayAtom ()

qidDoesNotBecomeLegalAtom : QIDEqualsLegalAtom → ⊥
qidDoesNotBecomeLegalAtom ()

deweyDoesNotCreateAuthority : DeweyEqualsAuthority → ⊥
deweyDoesNotCreateAuthority ()

regionalStudyDoesNotIdentifySpringviewPopulation : RegionalStudyEqualsSpringviewPopulation → ⊥
regionalStudyDoesNotIdentifySpringviewPopulation ()

reviewDoesNotBecomeIndependentObservation : ReviewEqualsIndependentObservation → ⊥
reviewDoesNotBecomeIndependentObservation ()

offsetModelDoesNotProveAdequacy : OffsetModelEqualsOffsetAdequacy → ⊥
offsetModelDoesNotProveAdequacy ()

citationsDoNotManufactureIndependence : MultipleCitationsEqualsIndependentCarriers → ⊥
citationsDoNotManufactureIndependence ()
