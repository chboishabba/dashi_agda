module DASHI.Law.SensibLawWoogarooIbrahimDeweyGraphParetoExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Wikimedia.DashiKnowledgeTraversalFunnelExact as Ibrahim
import DASHI.Law.SensibLawWoogarooEvidenceDependencyMatrixExact as Dependency
import DASHI.Law.SensibLawWoogarooLegalConsumerAtomCompletionExact as Atom

------------------------------------------------------------------------
-- WOOGAROO × IBRAHIM / DEWEY INVESTIGATIVE PARETO
--
-- Purpose:
--   * traverse outward from unpaid legal consumers rather than collect papers;
--   * retain DOI/QID/Dewey/primary-link coordinates separately;
--   * quotient repeated propositions sharing one upstream producer;
--   * prefer the source that pays the largest live dependency gap;
--   * never promote bibliographic adjacency into legal or ecological proof.
------------------------------------------------------------------------

data SourcePrimaryStatus : Set where
  primaryStatute : SourcePrimaryStatus
  primaryGovernmentRecord : SourcePrimaryStatus
  primaryEmpiricalArticle : SourcePrimaryStatus
  primaryProjectEvidence : SourcePrimaryStatus
  commissionedEmpiricalReport : SourcePrimaryStatus
  secondarySynthesis : SourcePrimaryStatus

data IdentifierState : Set where
  resolved : String → IdentifierState
  unresolved : IdentifierState
  notApplicable : IdentifierState

record SnowballCoordinate : Set where
  constructor snowball-coordinate
  field
    label : String
    primaryStatus : SourcePrimaryStatus
    doi : IdentifierState
    qid : IdentifierState
    topicQid : IdentifierState
    dewey : IdentifierState
    primaryLink : String
    formalisationRole : String
    legalConsumer : String
    firstUnpaidJoin : String

open SnowballCoordinate public

------------------------------------------------------------------------
-- Stable concept coordinates used by the graph. QIDs are semantic/search
-- coordinates only, following the Ibrahim boundary already owned in repo.
------------------------------------------------------------------------

koalaQid : String
koalaQid = "Q36101"

habitatFragmentationQid : String
habitatFragmentationQid = "Q913302"

wildlifeCorridorQid : String
wildlifeCorridorQid = "Q864912"

populationGeneticsQid : String
populationGeneticsQid = "Q31151"

conservationBiologyQid : String
conservationBiologyQid = "Q641498"

queenslandQid : String
queenslandQid = "Q36074"

animalEcologyDewey : String
animalEcologyDewey = "591.7"

geneticsDewey : String
geneticsDewey = "576.5"

ecologyDewey : String
ecologyDewey = "577"

biodiversityConservationDewey : String
biodiversityConservationDewey = "333.95"

------------------------------------------------------------------------
-- Primary statutory / project coordinates.
------------------------------------------------------------------------

nca102Coordinate : SnowballCoordinate
nca102Coordinate = snowball-coordinate
  "Nature Conservation Act 1992 (Qld), ss 12, 102-105"
  primaryStatute
  notApplicable
  unresolved
  (resolved queenslandQid)
  (resolved biodiversityConservationDewey)
  "https://www.legislation.qld.gov.au/view/whole/html/current/act-1992-020"
  "Primary legal consumer for threatening process, likely significant detrimental effect, land relation and duration of an interim conservation order."
  "NCA ss 102-107 interim conservation order"
  "Independent current ecological opinion applying the statutory wording to the approved process/current ecological state."

nca13Coordinate : SnowballCoordinate
nca13Coordinate = snowball-coordinate
  "Nature Conservation Act 1992 (Qld), s 13"
  primaryStatute
  notApplicable
  unresolved
  (resolved queenslandQid)
  (resolved biodiversityConservationDewey)
  "https://www.legislation.qld.gov.au/view/whole/html/current/act-1992-020"
  "Primary legal consumer defining critical habitat by essentiality to conservation of a viable protected-wildlife population/community."
  "NCA s 13 essentiality"
  "Independent viable-population identity joined to Springview/Woogaroo habitat function and a without-site counterfactual."

shgProjectCoordinate : SnowballCoordinate
shgProjectCoordinate = snowball-coordinate
  "Saunders Havill Group — Springview / EPBC 2019/8575 project ecology"
  primaryProjectEvidence
  notApplicable
  unresolved
  (resolved koalaQid)
  (resolved animalEcologyDewey)
  "project-specific corpus / SLQ legal-deposit lineage"
  "Same-project evidence for Koala occurrence, habitat score, connectivity, fragmentation, impact quantities and consultant significant-impact/recovery-value conclusions."
  "s 102 effect support + s 13 habitat-function support"
  "Needs genuinely independent current ecological/population evidence; repeated SHG propositions do not create another producer."

------------------------------------------------------------------------
-- Pareto scientific snowball.
------------------------------------------------------------------------

frere2023 : Source.AttributedSource
frere2023 = Source.mkDOISource
  "C. H. Frère; G. D. O'Reilly; K. Strickland; et al."
  "Evaluating the genetic consequences of population subdivision as it unfolds and how to best mitigate them: A rare story about koalas"
  "Molecular Ecology 32(9), 2174-2185"
  "2023"
  "10.1111/mec.16877"
  "https://doi.org/10.1111/mec.16877"
  Source.academicArticleSource
  "Independent empirical producer showing measurable genetic consequences of koala population subdivision and modelling dispersal needed to maintain connectivity; relevant to viable-population/corridor counterfactual design, not a same-object Springview finding."
  Source.publicAttribution

frere2023Coordinate : SnowballCoordinate
frere2023Coordinate = snowball-coordinate
  "Frère et al. 2023 — koala population subdivision"
  primaryEmpiricalArticle
  (resolved "10.1111/mec.16877")
  unresolved
  (resolved populationGeneticsQid)
  (resolved geneticsDewey)
  "https://doi.org/10.1111/mec.16877"
  "Highest-alpha methodological producer for turning corridor severance into measurable population-genetic consequences and a connectivity counterfactual."
  "NCA s 13 essentiality; supporting s 102 magnitude/duration analysis"
  "Same-region/same-population application remains unpaid; article is method/effect evidence, not Springview population identity."

mclennan2025 : Source.AttributedSource
mclennan2025 = Source.mkDOISource
  "Elspeth A. McLennan; Toby G. L. Kovacs; Luke W. Silver; Zhiliang Chen; Frederick R. Jaya; Simon Y. W. Ho; Katherine Belov; Carolyn J. Hogg"
  "Genomics identifies koala populations at risk across eastern Australia"
  "Ecological Applications 35(1), e3062"
  "2025"
  "10.1002/eap.3062"
  "https://doi.org/10.1002/eap.3062"
  Source.academicArticleSource
  "Primary genomic survey across eastern Australia; identifies isolation/genomic erosion and southeast-Queensland vulnerability. Supports population-scale framing but does not identify the Springview population by itself."
  Source.publicAttribution

mclennan2025Coordinate : SnowballCoordinate
mclennan2025Coordinate = snowball-coordinate
  "McLennan et al. 2025 — eastern-Australia koala genomics"
  primaryEmpiricalArticle
  (resolved "10.1002/eap.3062")
  unresolved
  (resolved populationGeneticsQid)
  (resolved geneticsDewey)
  "https://doi.org/10.1002/eap.3062"
  "Independent broad-scale producer connecting development, isolation and genomic erosion; useful to bound what a viable-population analysis should measure."
  "NCA s 13 essentiality"
  "Need sample/local-population linkage to Springfield/Woogaroo before treating its population findings as same-object evidence."

tacla2025 : Source.AttributedSource
tacla2025 = Source.mkDOISource
  "Philippa Kirsten Tacla; Benjamin James Barth; Sean Ian FitzGibbon; Amber Kristen Gillett; William Anthony Ellis"
  "Patterns of activity and travel by koalas in a disturbed urban landscape in Queensland"
  "Australian Mammalogy 47, AM24044"
  "2025"
  "10.1071/AM24044"
  "https://doi.org/10.1071/AM24044"
  Source.academicArticleSource
  "UQ empirical GPS/VHF study of koala movement in a changing southeast-Queensland urban landscape. Supports movement/connectivity mechanisms but is not Springview-specific."
  Source.publicAttribution

tacla2025Coordinate : SnowballCoordinate
tacla2025Coordinate = snowball-coordinate
  "Tacla et al. 2025 — disturbed urban Queensland movement"
  primaryEmpiricalArticle
  (resolved "10.1071/AM24044")
  unresolved
  (resolved koalaQid)
  (resolved animalEcologyDewey)
  "https://doi.org/10.1071/AM24044"
  "High-relevance Queensland movement producer for exposure, movement corridors and urban-fragmentation mechanisms."
  "NCA s 102 likely significant detrimental effect; NCA s 13 connectivity function"
  "Different population/site; transfer to Woogaroo requires an explicit applicability argument or local expert opinion."

rhodes2006 : Source.AttributedSource
rhodes2006 = Source.mkDOISource
  "Jonathan R. Rhodes; Thorsten Wiegand; Clive A. McAlpine; John Callaghan; Daniel Lunney; Michiala Bowen; Hugh P. Possingham"
  "Modeling species' distributions to improve conservation in semiurban landscapes: koala case study"
  "Conservation Biology 20(2), 449-459"
  "2006"
  "10.1111/j.1523-1739.2006.00330.x"
  "https://doi.org/10.1111/j.1523-1739.2006.00330.x"
  Source.academicArticleSource
  "UQ-led spatial model separating habitat quality from anthropogenic impacts in a semiurban koala landscape; useful as an older methodological anchor for current habitat-function/counterfactual modelling."
  Source.publicAttribution

rhodes2006Coordinate : SnowballCoordinate
rhodes2006Coordinate = snowball-coordinate
  "Rhodes et al. 2006 — semiurban koala distribution model"
  primaryEmpiricalArticle
  (resolved "10.1111/j.1523-1739.2006.00330.x")
  unresolved
  (resolved conservationBiologyQid)
  (resolved ecologyDewey)
  "https://doi.org/10.1111/j.1523-1739.2006.00330.x"
  "Method anchor for spatially separating natural habitat quality and anthropogenic pressure in semiurban koala conservation."
  "s 13 habitat-function counterfactual; supporting s 102 exposure analysis"
  "Methodological precedent only; not evidence that its fitted model applies unchanged at Woogaroo."

scenicRim2024 : Source.AttributedSource
scenicRim2024 = Source.mkNoDOISource
  "Federation University; WildDNA; QWAD Environment"
  "Scenic Rim 2024 Koala population study"
  "Scenic Rim Regional Council hosted technical report"
  "2024"
  "https://www.scenicrim.qld.gov.au/files/assets/public/v/1/our-environment/biodiversity/koalas/documents/scenicrim_2024koalastudyreport_final.pdf"
  Source.institutionalSource
  "Commissioned empirical southeast-Queensland population/genetic-connectivity study. Useful regional comparator for migration and connectivity; no DOI asserted."
  Source.publicAttribution

scenicRim2024Coordinate : SnowballCoordinate
scenicRim2024Coordinate = snowball-coordinate
  "Scenic Rim 2024 Koala population study"
  commissionedEmpiricalReport
  unresolved
  unresolved
  (resolved populationGeneticsQid)
  (resolved geneticsDewey)
  "https://www.scenicrim.qld.gov.au/files/assets/public/v/1/our-environment/biodiversity/koalas/documents/scenicrim_2024koalastudyreport_final.pdf"
  "Regional southeast-Queensland migration/connectivity comparator with direct management interpretation."
  "s 13 viable-population/corridor investigation"
  "Regional adjacency is not same-population identity; exact relationship to Woogaroo remains an acquisition question."

------------------------------------------------------------------------
-- Attributed source atlas. Paper-specific QIDs and Dewey numbers are not
-- invented: article QIDs remain unresolved unless independently paid; Dewey
-- coordinates below are topic-level classifications.
------------------------------------------------------------------------

woogarooIbrahimSourceAtlas : Source.AttributedSourceAtlas
woogarooIbrahimSourceAtlas = Source.mkSourceAtlas
  "Woogaroo Ibrahim/Dewey graph Pareto source atlas"
  "DASHI.Law.SensibLawWoogarooIbrahimDeweyGraphParetoExact"
  (frere2023 ∷ mclennan2025 ∷ tacla2025 ∷ rhodes2006 ∷ scenicRim2024 ∷ [])
  "Primary/commissioned scientific producers selected because they pay distinct live s 102/s 13 dependencies. DOI, QID, Dewey and link coordinates are kept separate; unresolved article QIDs are not inferred from topic identity; OEIS is not applicable to these ecological/legal consumers."

------------------------------------------------------------------------
-- Ibrahim-style knowledge graph nodes.
------------------------------------------------------------------------

s13KnowledgeNode : Ibrahim.DashiKnowledgeCoordinate
s13KnowledgeNode = Ibrahim.dashi-knowledge-coordinate
  "DASHI/Law/SensibLawWoogarooS13EssentialityStressTestExact.agda"
  "NCA s 13 statutory essentiality consumer"
  biodiversityConservationDewey
  koalaQid
  "Queensland Nature Conservation Act 1992 s 13"

populationGeneticsNode : Ibrahim.DashiKnowledgeCoordinate
populationGeneticsNode = Ibrahim.dashi-knowledge-coordinate
  "external/population-genetics"
  "population genetics literature"
  geneticsDewey
  populationGeneticsQid
  "10.1111/mec.16877"

fragmentationNode : Ibrahim.DashiKnowledgeCoordinate
fragmentationNode = Ibrahim.dashi-knowledge-coordinate
  "external/habitat-fragmentation"
  "fragmentation literature"
  ecologyDewey
  habitatFragmentationQid
  "10.1002/eap.3062"

corridorNode : Ibrahim.DashiKnowledgeCoordinate
corridorNode = Ibrahim.dashi-knowledge-coordinate
  "external/wildlife-corridor"
  "corridor/connectivity literature"
  ecologyDewey
  wildlifeCorridorQid
  "10.1071/AM24044"

s13ToPopulationGenetics : Ibrahim.DashiFirstLinkEdge
s13ToPopulationGenetics = Ibrahim.dashi-first-link-edge
  s13KnowledgeNode
  populationGeneticsNode
  Ibrahim.dependsOn
  Ibrahim.canonicalDashiFirstLinkPolicy
  "The first unpaid s 13 bridge is viable-population identity/essentiality, so population-genetic structure is preferred over another generic habitat map."
  true

populationGeneticsToFragmentation : Ibrahim.DashiFirstLinkEdge
populationGeneticsToFragmentation = Ibrahim.dashi-first-link-edge
  populationGeneticsNode
  fragmentationNode
  Ibrahim.dependsOn
  Ibrahim.canonicalDashiFirstLinkPolicy
  "Population subdivision and genetic erosion are linked to fragmentation; Frère and McLennan provide empirical producers rather than lexical adjacency."
  true

fragmentationToCorridor : Ibrahim.DashiFirstLinkEdge
fragmentationToCorridor = Ibrahim.dashi-first-link-edge
  fragmentationNode
  corridorNode
  Ibrahim.dependsOn
  Ibrahim.canonicalDashiFirstLinkPolicy
  "The live counterfactual asks whether Woogaroo connectivity is redundant or a bottleneck, so movement/corridor evidence is the next producer family."
  true

------------------------------------------------------------------------
-- Legal atom intersection.
------------------------------------------------------------------------

record SourcePaysAtomCandidate : Set where
  constructor source-pays-atom-candidate
  field
    sourceLabel : String
    atom : Atom.LegalExecutionAtom
    consumer : Atom.LegalExecutionConsumer
    admissibleAsEvidenceInput : Bool
    sameObjectPayment : Bool
    consumerAdequacyPaid : Bool
    exactRole : String

open SourcePaysAtomCandidate public

frereForS13 : SourcePaysAtomCandidate
frereForS13 = source-pays-atom-candidate
  "Frère et al. 2023"
  Atom.habitatPopulationEssentialityAtom
  Atom.nca13EssentialityConsumer
  true false false
  "Pays a methodological/empirical producer for consequences of population subdivision and connectivity maintenance; does not identify the Woogaroo viable population or prove this habitat essential."

taclaForS102 : SourcePaysAtomCandidate
taclaForS102 = source-pays-atom-candidate
  "Tacla et al. 2025"
  Atom.likelySignificantDetrimentalEffectAtom
  Atom.nca102InterimOrderConsumer
  true false false
  "Pays an independent Queensland movement/urban-fragmentation evidence input; same-object effect on 9281/Woogaroo remains for current expert opinion."

scenicForS13 : SourcePaysAtomCandidate
scenicForS13 = source-pays-atom-candidate
  "Scenic Rim 2024 Koala population study"
  Atom.habitatPopulationEssentialityAtom
  Atom.nca13EssentialityConsumer
  true false false
  "Pays a regional SEQ population/genetic-connectivity comparator; adjacency does not establish the Springview population identity."

------------------------------------------------------------------------
-- Investigative Pareto: acquisition value is consumer-gap closure, source
-- independence and same-object proximity, not document count or centrality.
------------------------------------------------------------------------

data ParetoPriority : Set where
  P0 : ParetoPriority
  P1 : ParetoPriority
  P2 : ParetoPriority
  P3 : ParetoPriority

record InvestigativeParetoTarget : Set where
  constructor investigative-pareto-target
  field
    priority : ParetoPriority
    target : String
    whyNow : String
    sourceFamily : String
    expectedConsumerGain : String
    stopCondition : String

open InvestigativeParetoTarget public

p0CurrentExpert : InvestigativeParetoTarget
p0CurrentExpert = investigative-pareto-target
  P0
  "Independent current ecological opinion applying NCA ss 12/102 and s 13 to the exact approved process/current Woogaroo ecological state"
  "It is both independent of SHG and closest to the same-object legal consumers."
  "local/current koala ecologist with population/connectivity competence"
  "Can directly address likely significant detrimental effect and identify the biologically relevant population/essentiality evidence still required."
  "Stop broad literature acquisition once a defensible current same-object expert opinion and its evidence basis are obtained."

p1PopulationIdentity : InvestigativeParetoTarget
p1PopulationIdentity = investigative-pareto-target
  P1
  "Identify the viable Koala population/community spanning Springfield/Woogaroo using existing survey/genetic/monitoring datasets"
  "This is the first unpaid s 13 same-object join."
  "NKMP / Queensland monitoring / regional genetic studies / local survey datasets"
  "Turns site habitat evidence into a population-level counterfactual rather than another habitat-description layer."
  "Stop when population identity/boundary is evidenced strongly enough for an ecologist to evaluate loss/severance."

p2ConnectivityCounterfactual : InvestigativeParetoTarget
p2ConnectivityCounterfactual = investigative-pareto-target
  P2
  "Quantify the without-Woogaroo connectivity counterfactual"
  "Frère 2023 and later genomics show measurable consequences of subdivision, but Woogaroo's bottleneck/redundancy remains unpaid."
  "movement/genetics + GIS/LES + current habitat network"
  "Pays magnitude, duration, reversibility and substitutability inputs for s 102 and essentiality for s 13."
  "Stop when removal/severance can be compared against an explicit present-day alternative-connectivity scenario."

p3MoreGeneralLiterature : InvestigativeParetoTarget
p3MoreGeneralLiterature = investigative-pareto-target
  P3
  "Additional generic koala fragmentation literature"
  "Useful only if it adds a new producer, method or unresolved mechanism."
  "general literature"
  "Low marginal gain once current SOTA method families are represented."
  "Do not collect another paper merely because it repeats fragmentation harms already paid by independent producers."

------------------------------------------------------------------------
-- Independence and identifier firewalls.
------------------------------------------------------------------------

data DOIEqualsProof : Set where
data QidEqualsSameObject : Set where
data DeweyEqualsSemanticDependency : Set where
data TopicQidEqualsPaperQid : Set where
data RegionalStudyEqualsWoogarooPopulation : Set where
data LiteratureMultiplicityEqualsIndependentCorroboration : Set where
data SotaPaperEqualsLegalAtomPaid : Set where

doiDoesNotCreateProof : DOIEqualsProof → ⊥
doiDoesNotCreateProof ()

qidDoesNotCreateSameObject : QidEqualsSameObject → ⊥
qidDoesNotCreateSameObject ()

deweyDoesNotCreateDependency : DeweyEqualsSemanticDependency → ⊥
deweyDoesNotCreateDependency ()

topicQidDoesNotBecomePaperQid : TopicQidEqualsPaperQid → ⊥
topicQidDoesNotBecomePaperQid ()

regionalStudyDoesNotCreateWoogarooPopulationIdentity : RegionalStudyEqualsWoogarooPopulation → ⊥
regionalStudyDoesNotCreateWoogarooPopulation ()

morePapersDoNotCreateIndependentCorroboration : LiteratureMultiplicityEqualsIndependentCorroboration → ⊥
morePapersDoNotCreateIndependentCorroboration ()

sotaDoesNotAutoPayLegalAtom : SotaPaperEqualsLegalAtomPaid → ⊥
sotaDoesNotAutoPayLegalAtom ()

------------------------------------------------------------------------
-- Existing dependency matrix remains authoritative for payment state.
------------------------------------------------------------------------

currentS13Dependency : Dependency.ConsumerDependencyState
currentS13Dependency = Dependency.s13DependencyState

currentS102Dependency : Dependency.ConsumerDependencyState
currentS102Dependency = Dependency.s102DependencyState
