module DASHI.Law.SensibLawWoogarooIbrahimSnowballLegalAtomExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Wikimedia.IdentifierExact as Wiki
import DASHI.Law.SensibLawWoogarooAdmissibleFactorsWrongTypeAtomBridgeExact as AFW
import DASHI.Law.SensibLawWoogarooLegalConsumerAtomCompletionExact as Atom
import DASHI.Law.SensibLawWoogarooEvidenceDependencyMatrixExact as Dependency

------------------------------------------------------------------------
-- WOOGAROO IBRAHIM-STYLE SOURCE SNOWBALL × LEGAL ATOM BRIDGE
--
-- The Ibrahim discipline is followed explicitly:
--   source identity / author / title / DOI / QID / Dewey / source role /
--   primary-v-secondary status / acquisition order / dependency relation /
--   consumer-specific legal atom / residual.
--
-- Acquisition order may snowball broadly.  Payment order may not skip a
-- missing identity, same-object, independence, or consumer-specific bridge.
------------------------------------------------------------------------

data SnowballPrimaryStatus : Set where
  primaryStatute : SnowballPrimaryStatus
  primaryGovernmentStatus : SnowballPrimaryStatus
  primaryPeerReviewedStudy : SnowballPrimaryStatus
  secondaryInstitutionalSummary : SnowballPrimaryStatus

data QidState : Set where
  qidRecorded : Wiki.ItemId → QidState
  qidUnresolved : QidState

data DeweyState : Set where
  deweyRecorded : String → DeweyState
  deweyUnresolved : DeweyState

data SnowballConsumer : Set where
  s102ThreatenedWildlifeGateway : SnowballConsumer
  s102ThreateningProcess : SnowballConsumer
  s102LikelySignificantDetrimentalEffect : SnowballConsumer
  s13HabitatFunction : SnowballConsumer
  s13ViablePopulationIdentity : SnowballConsumer
  s13Essentiality : SnowballConsumer
  s43BHistoricalClearing : SnowballConsumer

data SnowballEvidenceRole : Set where
  legalRuleRole : SnowballEvidenceRole
  threatenedStatusRole : SnowballEvidenceRole
  regionalPopulationGeneticsRole : SnowballEvidenceRole
  landscapeConnectivityRole : SnowballEvidenceRole
  localHabitatUseRole : SnowballEvidenceRole
  urbanMortalityRole : SnowballEvidenceRole
  projectSpecificEcologyRole : SnowballEvidenceRole
  methodOrComparatorRole : SnowballEvidenceRole

record SnowballSourceReceipt : Set where
  constructor snowball-source-receipt
  field
    source : Source.AttributedSource
    primaryStatus : SnowballPrimaryStatus
    qid : QidState
    dewey : DeweyState
    evidenceRole : SnowballEvidenceRole
    consumer : SnowballConsumer
    boundedUse : String
    sourceIndependence : String
    doesNotPay : String

open SnowballSourceReceipt public

------------------------------------------------------------------------
-- Stable concept identifiers.  QIDs classify entities/concepts; they are not
-- publication identity, scientific truth, source authority, or legal effect.
------------------------------------------------------------------------

koalaQid : Wiki.ItemId
koalaQid = Wiki.itemId "Q36101"

geneFlowQid : Wiki.ItemId
geneFlowQid = Wiki.itemId "Q143089"

habitatFragmentationQid : Wiki.ItemId
habitatFragmentationQid = Wiki.itemId "Q913302"

wildlifeCorridorQid : Wiki.ItemId
wildlifeCorridorQid = Wiki.itemId "Q864912"

endangeredSpeciesQid : Wiki.ItemId
endangeredSpeciesQid = Wiki.itemId "Q11394"

------------------------------------------------------------------------
-- Primary legal / government sources.
------------------------------------------------------------------------

ncaS102Source : Source.AttributedSource
ncaS102Source = Source.mkNoDOISource
  "Queensland Parliamentary Counsel"
  "Nature Conservation Act 1992 — sections 12, 102–105"
  "Queensland Legislation — current in-force text"
  "2026"
  "https://www.legislation.qld.gov.au/view/whole/html/current/act-1992-020"
  Source.governmentSource
  "Primary law for threatening process, interim conservation order gateway, order content/spatial reach and duration."
  Source.publicAttribution

ncaS13Source : Source.AttributedSource
ncaS13Source = Source.mkNoDOISource
  "Queensland Parliamentary Counsel"
  "Nature Conservation Act 1992 — section 13"
  "Queensland Legislation — current in-force text"
  "2026"
  "https://www.legislation.qld.gov.au/view/whole/html/current/act-1992-020"
  Source.governmentSource
  "Primary law defining critical habitat by essentiality to conservation of a viable protected-wildlife population or native-wildlife community."
  Source.publicAttribution

qldKoalaStatusSource : Source.AttributedSource
qldKoalaStatusSource = Source.mkNoDOISource
  "Queensland Government"
  "Changes made to wildlife categories on 8 April 2022"
  "Queensland threatened-species conservation-status material"
  "2022"
  "https://www.qld.gov.au/environment/plants-animals/conservation/threatened-species/classes/conservation-status/changes-categories-april-2022"
  Source.governmentSource
  "Primary government source for Queensland Endangered status of Phascolarctos cinereus."
  Source.publicAttribution

ncaS102Receipt : SnowballSourceReceipt
ncaS102Receipt = snowball-source-receipt
  ncaS102Source
  primaryStatute
  qidUnresolved
  (deweyRecorded "340")
  legalRuleRole
  s102LikelySignificantDetrimentalEffect
  "Pays statutory wording and duration/spatial structure only."
  "Legally independent of project ecology."
  "Does not provide ecological corroboration, current execution facts or the Ministerial opinion."

ncaS13Receipt : SnowballSourceReceipt
ncaS13Receipt = snowball-source-receipt
  ncaS13Source
  primaryStatute
  qidUnresolved
  (deweyRecorded "340")
  legalRuleRole
  s13Essentiality
  "Pays the statutory essentiality consumer only."
  "Legally independent of project ecology."
  "Does not identify the relevant viable Koala population or prove site essentiality."

koalaStatusReceipt : SnowballSourceReceipt
koalaStatusReceipt = snowball-source-receipt
  qldKoalaStatusSource
  primaryGovernmentStatus
  (qidRecorded koalaQid)
  (deweyRecorded "333.95")
  threatenedStatusRole
  s102ThreatenedWildlifeGateway
  "Pays Queensland threatened-wildlife status for Koala."
  "Institutionally independent of SHG project ecology."
  "Does not pay project exposure, threatening process, significant detrimental effect or s 13 essentiality."

------------------------------------------------------------------------
-- Primary peer-reviewed scientific snowball.
------------------------------------------------------------------------

fowler2000 : Source.AttributedSource
fowler2000 = Source.mkDOISource
  "E. V. Fowler; B. A. Houlden; P. Hoeben; P. Timms"
  "Genetic diversity and gene flow among southeastern Queensland koalas (Phascolarctos cinereus)"
  "Molecular Ecology 9(2):155–164"
  "2000"
  "10.1046/j.1365-294x.2000.00844.x"
  "https://pubmed.ncbi.nlm.nih.gov/10672159/"
  Source.academicArticleSource
  "Regional primary genetic evidence from 96 Koalas across five southeast-Queensland populations; used to establish that population structure/gene flow must be treated as an empirical object rather than inferred from one development boundary."
  Source.publicAttribution

rhodes2006 : Source.AttributedSource
rhodes2006 = Source.mkDOISource
  "Jonathan R. Rhodes; Thorsten Wiegand; Clive A. McAlpine; John Callaghan; Daniel Lunney; Michiala Bowen; Hugh P. Possingham"
  "Modeling species' distributions to improve conservation in semiurban landscapes: koala case study"
  "Conservation Biology 20(2):449–459"
  "2006"
  "10.1111/j.1523-1739.2006.00330.x"
  "https://pubmed.ncbi.nlm.nih.gov/16903106/"
  Source.academicArticleSource
  "Primary semiurban Koala distribution study separating natural habitat quality from anthropogenic impacts; used as method/context for spatially explicit site/population reasoning."
  Source.publicAttribution

dudaniec2013 : Source.AttributedSource
dudaniec2013 = Source.mkDOISource
  "Rachael Y. Dudaniec; Jonathan R. Rhodes; Jessica Worthington Wilmer; Mitchell Lyons; Kristen E. Lee; Clive A. McAlpine; Frank N. Carrick"
  "Using multilevel models to identify drivers of landscape-genetic structure among management areas"
  "Molecular Ecology 22(14):3752–3765"
  "2013"
  "10.1111/mec.12359"
  "https://pubmed.ncbi.nlm.nih.gov/23730800/"
  Source.academicArticleSource
  "Primary southeast-Queensland landscape-genetics study linking management-scale landscape structure to Koala genetic connectivity."
  Source.publicAttribution

edgar2018 : Source.AttributedSource
edgar2018 = Source.mkDOISource
  "J. P. Edgar; D. N. Jones"
  "Individuals matter: predicting koala road crossing behaviour in south-east Queensland"
  "Australian Mammalogy 40(1):67–75"
  "2018"
  "10.1071/AM16043"
  "https://doi.org/10.1071/AM16043"
  Source.academicArticleSource
  "Primary movement/road-crossing study across six southeast-Queensland subpopulations; used for movement/barrier mechanism, not Springview-specific occurrence."
  Source.publicAttribution

mclennan2025 : Source.AttributedSource
mclennan2025 = Source.mkDOISource
  "Elspeth A. McLennan; Toby G. L. Kovacs; Luke W. Silver; Zhiliang Chen; Frederick R. Jaya; Simon Y. W. Ho; Katherine Belov; Carolyn J. Hogg"
  "Genomics identifies koala populations at risk across eastern Australia"
  "Ecological Applications 35(1):e3062"
  "2025"
  "10.1002/eap.3062"
  "https://doi.org/10.1002/eap.3062"
  Source.academicArticleSource
  "Primary whole-genome population study; used to bound current regional population structure, genomic erosion, inbreeding and the importance of connectivity without asserting a Springview-specific population identity."
  Source.publicAttribution

fowlerReceipt : SnowballSourceReceipt
fowlerReceipt = snowball-source-receipt
  fowler2000 primaryPeerReviewedStudy
  (qidRecorded koalaQid)
  (deweyRecorded "576.5")
  regionalPopulationGeneticsRole
  s13ViablePopulationIdentity
  "Supports the proposition that southeast-Queensland Koalas are empirically structured populations with measurable gene flow/heterogeneity."
  "Independent historical genetic sample from the SHG development ecology."
  "Does not identify the present Springview/Opossum-Woogaroo viable population."

rhodesReceipt : SnowballSourceReceipt
rhodesReceipt = snowball-source-receipt
  rhodes2006 primaryPeerReviewedStudy
  (qidRecorded koalaQid)
  (deweyRecorded "333.95")
  landscapeConnectivityRole
  s13HabitatFunction
  "Supports spatially explicit separation of natural habitat quality and anthropogenic impacts in semiurban Koala conservation."
  "Independent research lineage from SHG project ecology."
  "Does not prove the exact Springview habitat is essential or that s 102 is satisfied."

dudaniecReceipt : SnowballSourceReceipt
dudaniecReceipt = snowball-source-receipt
  dudaniec2013 primaryPeerReviewedStudy
  (qidRecorded geneFlowQid)
  (deweyRecorded "576.5")
  regionalPopulationGeneticsRole
  s13ViablePopulationIdentity
  "Supports management-scale analysis of landscape drivers of Koala gene flow and gives a principled route for defining population/connectivity beyond a development boundary."
  "Independent primary landscape-genetic dataset from SHG project ecology."
  "Does not pay local population identity, current gene flow or site essentiality."

edgarReceipt : SnowballSourceReceipt
edgarReceipt = snowball-source-receipt
  edgar2018 primaryPeerReviewedStudy
  (qidRecorded koalaQid)
  (deweyRecorded "333.95")
  landscapeConnectivityRole
  s102LikelySignificantDetrimentalEffect
  "Supports a mechanism by which roads/fragmentation interact with individual Koala movement in southeast Queensland."
  "Independent behavioural dataset from SHG project ecology."
  "Does not establish current movement through Springview or quantify the effect of 9281."

mclennanReceipt : SnowballSourceReceipt
mclennanReceipt = snowball-source-receipt
  mclennan2025 primaryPeerReviewedStudy
  (qidRecorded geneFlowQid)
  (deweyRecorded "576.5")
  regionalPopulationGeneticsRole
  s13ViablePopulationIdentity
  "Current broad-scale genomic evidence that habitat destruction/alteration and linear/sprawled infrastructure can isolate Koala populations and reduce gene flow/adaptive potential, including southeast-Queensland patterns."
  "Independent whole-genome survey; distinct upstream carrier from historical SHG site ecology."
  "Does not identify a Springview-local viable population or prove that this exact site is a bottleneck."

------------------------------------------------------------------------
-- Secondary institutional signpost.  Kept separate from the primary paper.
------------------------------------------------------------------------

uq2014Summary : Source.AttributedSource
uq2014Summary = Source.mkNoDOISource
  "The University of Queensland"
  "Better urban planning can save koalas"
  "UQ News"
  "2014"
  "https://news.uq.edu.au/article/2014/03/better-urban-planning-can-save-koalas"
  Source.institutionalSource
  "Secondary institutional summary/signpost to Dudaniec et al. 2013; useful for acquisition and plain-language interpretation, not a second independent scientific producer."
  Source.publicAttribution

uq2014Receipt : SnowballSourceReceipt
uq2014Receipt = snowball-source-receipt
  uq2014Summary secondaryInstitutionalSummary
  (qidRecorded geneFlowQid)
  (deweyRecorded "576.5")
  methodOrComparatorRole
  s13ViablePopulationIdentity
  "Acquisition/interpretation signpost for the primary landscape-genetics paper."
  "Derives from/reports the Dudaniec et al. study rather than independently reproducing it."
  "Must not be counted as an additional independent genetic evidence stream."

------------------------------------------------------------------------
-- Concept snowball: identifiers are navigational/entity metadata only.
------------------------------------------------------------------------

record ConceptSnowball : Set where
  constructor concept-snowball
  field
    label : String
    qid : Wiki.ItemId
    dewey : String
    legalUse : String
    boundary : String

open ConceptSnowball public

koalaConcept : ConceptSnowball
koalaConcept = concept-snowball
  "Koala / Phascolarctos cinereus" koalaQid "599.2"
  "Taxon identity for status, occurrence, habitat and population evidence."
  "Taxon identity does not establish occurrence at Springview, population identity or legal significance."

geneFlowConcept : ConceptSnowball
geneFlowConcept = concept-snowball
  "gene flow" geneFlowQid "576.5"
  "Population-connectivity observable relevant to viable-population identification."
  "Gene-flow literature does not manufacture local gene-flow measurements."

fragmentationConcept : ConceptSnowball
fragmentationConcept = concept-snowball
  "habitat fragmentation" habitatFragmentationQid "577"
  "Mechanism linking development/linear infrastructure to habitat-function and population effects."
  "Fragmentation as a general concept does not establish magnitude or legal significance at this site."

corridorConcept : ConceptSnowball
corridorConcept = concept-snowball
  "wildlife corridor" wildlifeCorridorQid "333.95"
  "Functional connectivity concept for site/population and threatening-process analysis."
  "A mapped corridor label does not by itself establish s 13 essentiality or s 102 detrimental effect."

endangeredConcept : ConceptSnowball
endangeredConcept = concept-snowball
  "endangered species" endangeredSpeciesQid "333.95"
  "Conservation-status concept; exact Queensland legal status remains paid by the Queensland Government source."
  "Generic Wikidata endangered status is not a substitute for the operative Queensland listing."

------------------------------------------------------------------------
-- Intersect the Snowball with the canonical Woogaroo legal atoms.
------------------------------------------------------------------------

record LegalAtomSnowballBridge : Set where
  constructor legal-atom-snowball-bridge
  field
    consumer : SnowballConsumer
    canonicalExistingAtom : String
    canonicalExecutionAtom : String
    currentlySourcePaid : Bool
    independentSciencePaid : Bool
    sameObjectLocalJoinPaid : Bool
    firstUnpaid : String

open LegalAtomSnowballBridge public

s102AtomBridge : LegalAtomSnowballBridge
s102AtomBridge = legal-atom-snowball-bridge
  s102LikelySignificantDetrimentalEffect
  "AFW.threatenedSpeciesPresenceAtom + approved-process/geometry owners"
  "Atom.likelySignificantDetrimentalEffectAtom"
  true
  true
  false
  "Obtain a current independent ecological opinion that applies the Queensland s 12/s 102 wording to the exact approved 9281 process and current Springview/Woogaroo ecological state; regional literature informs the method and causal mechanism but cannot substitute for the local same-object opinion."

s13AtomBridge : LegalAtomSnowballBridge
s13AtomBridge = legal-atom-snowball-bridge
  s13Essentiality
  "AFW.exactParcelHabitatFunctionAtom"
  "Atom.habitatPopulationEssentialityAtom"
  true
  true
  false
  "Identify the biologically relevant viable Koala population/community independently of the development boundary, then test the without-site/severance counterfactual for persistence, movement, breeding/dispersal and resource access."

------------------------------------------------------------------------
-- Dependency accounting: publication count is not producer count.
------------------------------------------------------------------------

record IbrahimSnowballDependencyState : Set where
  constructor ibrahim-snowball-dependency-state
  field
    primaryPeerReviewedSources : Nat
    secondarySignposts : Nat
    stableConceptQids : Nat
    sourceFamiliesIndependentOfSHG : Nat
    localSpringviewPopulationStudyPaid : Bool
    localCurrentExpertOpinionPaid : Bool
    acquisitionMaySnowballOutOfOrder : Bool
    paymentMaySkipIdentityDependency : Bool

currentIbrahimSnowballDependencyState : IbrahimSnowballDependencyState
currentIbrahimSnowballDependencyState = ibrahim-snowball-dependency-state
  5 1 5 5 false false true false

existingDependencyMatrix : Dependency.ConsumerDependencyState
existingDependencyMatrix = Dependency.s13DependencyState

------------------------------------------------------------------------
-- Attribution / WrongType firewalls.
------------------------------------------------------------------------

data DOIEqualsScientificTruth : Set where
data QidEqualsClaimTruth : Set where
data DeweyEqualsSourceRole : Set where
data SecondarySummaryEqualsIndependentProducer : Set where
data RegionalGeneticsEqualsLocalPopulationIdentity : Set where
data GeneralConnectivityScienceEqualsSiteEssentiality : Set where
data PrimaryPaperEqualsLegalConclusion : Set where
data MultiplePapersEqualsSameObjectJoin : Set where

DOIDoesNotCreateTruth : DOIEqualsScientificTruth → ⊥
DOIDoesNotCreateTruth ()

qidDoesNotCreateTruth : QidEqualsClaimTruth → ⊥
qidDoesNotCreateTruth ()

deweyDoesNotCreateSourceRole : DeweyEqualsSourceRole → ⊥
deweyDoesNotCreateSourceRole ()

secondaryDoesNotCreateIndependentProducer : SecondarySummaryEqualsIndependentProducer → ⊥
secondaryDoesNotCreateIndependentProducer ()

regionalGeneticsDoesNotIdentifyLocalPopulation : RegionalGeneticsEqualsLocalPopulationIdentity → ⊥
regionalGeneticsDoesNotIdentifyLocalPopulation ()

connectivityScienceDoesNotCreateEssentiality : GeneralConnectivityScienceEqualsSiteEssentiality → ⊥
connectivityScienceDoesNotCreateEssentiality ()

paperDoesNotCreateLegalConclusion : PrimaryPaperEqualsLegalConclusion → ⊥
paperDoesNotCreateLegalConclusion ()

paperMultiplicityDoesNotPaySameObjectJoin : MultiplePapersEqualsSameObjectJoin → ⊥
paperMultiplicityDoesNotPaySameObjectJoin ()

------------------------------------------------------------------------
-- Source atlas for repository-wide acquisition/navigation.
------------------------------------------------------------------------

woogarooIbrahimSnowballAtlas : Source.AttributedSourceAtlas
woogarooIbrahimSnowballAtlas = Source.mkSourceAtlas
  "Woogaroo s102/s13 Ibrahim-style source snowball"
  "DASHI.Law.SensibLawWoogarooIbrahimSnowballLegalAtomExact"
  (ncaS102Source ∷ ncaS13Source ∷ qldKoalaStatusSource ∷
   fowler2000 ∷ rhodes2006 ∷ dudaniec2013 ∷ edgar2018 ∷ mclennan2025 ∷
   uq2014Summary ∷ [])
  "Primary law/status plus primary peer-reviewed southeast-Queensland/population-connectivity science, with UQ secondary material retained only as a signpost. DOI/QID/Dewey metadata support identity/navigation and do not import proof or authority."
