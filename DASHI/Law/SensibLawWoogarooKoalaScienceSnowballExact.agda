module DASHI.Law.SensibLawWoogarooKoalaScienceSnowballExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Source

------------------------------------------------------------------------
-- WOOGAROO KOALA SCIENCE SNOWBALL
--
-- Current scientific/methodological context for the live s 102 and s 13
-- consumers. These sources support mechanisms, methods and counterfactual
-- questions. They are not same-object evidence about Springview unless an
-- exact local study/data join is independently paid.
------------------------------------------------------------------------

data ScienceUse : Set where
  habitatDefinitionAndSurvey : ScienceUse
  connectivityMethodology : ScienceUse
  fragmentationMechanism : ScienceUse
  populationGenomics : ScienceUse
  urbanMovementRisk : ScienceUse
  mitigationEvaluation : ScienceUse
  restorationSubstitutability : ScienceUse

data ApplicabilityClass : Set where
  officialGeneralGuidance : ApplicabilityClass
  peerReviewedGeneralMechanism : ApplicabilityClass
  southEastQueenslandRegionalEvidence : ApplicabilityClass
  sameObjectLocalEvidence : ApplicabilityClass

record ScienceSnowballEntry : Set where
  constructor science-snowball-entry
  field
    source : Source.AttributedSource
    use : ScienceUse
    applicability : ApplicabilityClass
    boundedFinding : String
    s102Use : String
    s13Use : String
    localResidual : String

open ScienceSnowballEntry public

endangeredKoalaHabitatGuidance : ScienceSnowballEntry
endangeredKoalaHabitatGuidance = science-snowball-entry
  (Source.mkNoDOISource
    "Department of Climate Change, Energy, the Environment and Water"
    "Identifying habitat for the endangered Koala"
    "Australian Government koala habitat guidance"
    "2025"
    "https://www.dcceew.gov.au/environment/epbc/publications/identifying-habitat-for-the-endangered-koala"
    Source.governmentSource
    "Current official synthesis: koala habitat is landscape-context dependent and includes feed trees, movement ground, corridors and connectivity; unoccupied habitat may still be habitat."
    Source.publicAttribution)
  habitatDefinitionAndSurvey
  officialGeneralGuidance
  "Habitat is not merely occupied trees. The guidance treats landscape arrangement, movement between patches, riparian/climate-refuge attributes and metapopulation processes as relevant habitat attributes."
  "Supports the ecological plausibility of indirect/fragmentation effects extending beyond a tree-by-tree clearing footprint."
  "Supports asking whether Springview/Opossum-Woogaroo habitat contributes movement, resource and metapopulation functions required by a viable population."
  "It does not identify the exact Springview population or prove a statutory conclusion."

koalaRecoveryPlan : ScienceSnowballEntry
koalaRecoveryPlan = science-snowball-entry
  (Source.mkNoDOISource
    "Department of Agriculture, Water and the Environment"
    "National Recovery Plan for the Koala Phascolarctos cinereus (combined populations of Queensland, New South Wales and the Australian Capital Territory)"
    "Australian Government national recovery plan"
    "2022"
    "https://www.dcceew.gov.au/environment/biodiversity/threatened/publications/recovery/koala-2022"
    Source.governmentSource
    "National landscape-scale recovery framework emphasising resilient, connected and genetically healthy metapopulations and increased habitat extent, quality and connectivity."
    Source.publicAttribution)
  connectivityMethodology
  officialGeneralGuidance
  "The recovery goal is explicitly population- and connectivity-oriented rather than limited to isolated occupied patches."
  "Supports treating fragmentation/connectivity loss as a biologically material pathway requiring expert assessment."
  "Supports defining the relevant viable population/community in landscape/metapopulation terms rather than equating it with the development boundary."
  "The recovery plan is not an NCA s 13 declaration and does not identify Springview as essential habitat."

koalaHabitatMethodsReview : ScienceSnowballEntry
koalaHabitatMethodsReview = science-snowball-entry
  (Source.mkNoDOISource
    "Kara N. Youngentob; Karen J. Marsh; James Skewes"
    "A review of koala habitat assessment criteria and methods"
    "Australian National University report prepared for the Australian Government"
    "2021"
    "https://www.dcceew.gov.au/environment/epbc/publications/review-koala-habitat-assessment-criteria-and-methods"
    Source.institutionalSource
    "Method review for habitat, presence and abundance assessment, including survey limitations and the need to avoid equating non-detection with absence."
    Source.publicAttribution)
  habitatDefinitionAndSurvey
  officialGeneralGuidance
  "No single survey method is universally adequate; true absence requires stronger repeated/multiple-method evidence than a one-off non-detection."
  "Supports careful treatment of historical survey negatives and current survey adequacy when assessing likely effect."
  "Supports refusing to infer that apparently low observed abundance means the landscape lacks population-level conservation function."
  "It does not convert any particular Springview survey into inadequate evidence without same-method review."

bruntonConnectivityReview : ScienceSnowballEntry
bruntonConnectivityReview = science-snowball-entry
  (Source.mkDOISource
    "Elizabeth A. Brunton; Katrin Hohwieler; Kye McDonald; Romane H. Cristescu"
    "Mapping connectivity for conservation of a threatened iconic mammal, the koala: Trends, challenges and opportunities"
    "Ecological Solutions and Evidence 7(2), e70253"
    "2026"
    "10.1002/2688-8319.70253"
    "https://doi.org/10.1002/2688-8319.70253"
    Source.academicArticleSource
    "State-of-the-art review of koala connectivity mapping; highlights the conservation importance of connectivity and warns that available maps can exceed the supporting ecological data."
    Source.publicAttribution)
  connectivityMethodology
  peerReviewedGeneralMechanism
  "Connectivity is central to conservation, but model/map availability must not be confused with realised functional connectivity; ecological validation is a separate obligation."
  "Supports using corridor/fragmentation mapping as evidence while retaining a separate causal/functional validation step."
  "Directly informs the s 13 question whether the mapped connection is functionally important to a viable population rather than merely cartographic proximity."
  "The review does not validate the Woogaroo corridor or identify the local population."

frereSubdivisionStudy : ScienceSnowballEntry
frereSubdivisionStudy = science-snowball-entry
  (Source.mkDOISource
    "C. H. Frère; G. D. O'Reilly; K. Strickland; A. Schultz; K. Hohwieler; J. Hanger; D. de Villiers; R. Cristescu; D. Powell; W. Sherwin"
    "Evaluating the genetic consequences of population subdivision as it unfolds and how to best mitigate them: A rare story about koalas"
    "Molecular Ecology 32(9), 2174-2185"
    "2023"
    "10.1111/mec.16877"
    "https://doi.org/10.1111/mec.16877"
    Source.academicArticleSource
    "Empirical population-genetic study of koala subdivision associated with linear infrastructure, including mitigation evaluation through dispersal/gene-flow requirements."
    Source.publicAttribution)
  mitigationEvaluation
  peerReviewedGeneralMechanism
  "Population subdivision can reduce effective population size and allelic richness; mitigation adequacy can be evaluated in terms of realised dispersal/gene flow rather than the mere presence of crossings or retained strips."
  "Supports testing whether proposed mitigation actually maintains movement/connectivity rather than treating mitigation existence as proof of no significant effect."
  "Provides a biologically grounded way to ask whether Springview habitat loss/severance materially impairs viable-population connectivity."
  "Its study population/infrastructure are not Springview; numeric thresholds cannot be transplanted without a same-population model."

mclennanGenomicsStudy : ScienceSnowballEntry
mclennanGenomicsStudy = science-snowball-entry
  (Source.mkDOISource
    "Elspeth A. McLennan; Toby G. L. Kovacs; Luke W. Silver; Zhiliang Chen; Frederick R. Jaya; Simon Y. W. Ho; Katherine Belov; Carolyn J. Hogg"
    "Genomics identifies koala populations at risk across eastern Australia"
    "Ecological Applications 35(1), e3062"
    "2025"
    "10.1002/eap.3062"
    "https://doi.org/10.1002/eap.3062"
    Source.academicArticleSource
    "Range-wide genomic analysis identifying isolation/genomic erosion concerns, including coastal southeast Queensland, and highlighting infrastructure/habitat destruction as barriers to dispersal."
    Source.publicAttribution)
  populationGenomics
  southEastQueenslandRegionalEvidence
  "Genomic vulnerability is not abstract: coastal southeast Queensland includes populations with low diversity/high inbreeding concern, and continued habitat fragmentation can worsen isolation."
  "Supports treating further fragmentation in SEQ as a credible harm pathway requiring local assessment."
  "Supports the importance of defining the relevant local/regional population and its connectivity before deciding whether habitat is substitutable."
  "The paper does not identify the Springview/Opossum-Woogaroo koalas as a specific sampled genomic population."

dexterSEQVehicleStrikeStudy : ScienceSnowballEntry
dexterSEQVehicleStrikeStudy = science-snowball-entry
  (Source.mkDOISource
    "C. E. Dexter; J. Scott; A. R. F. Blacker; R. G. Appleby; D. H. Kerlin; D. N. Jones"
    "Koalas in space and time: Lessons from 20 years of vehicle-strike trends and hot spots in South East Queensland"
    "Austral Ecology 49, e13465"
    "2024"
    "10.1111/aec.13465"
    "https://doi.org/10.1111/aec.13465"
    Source.academicArticleSource
    "South East Queensland evidence that road-risk patterns change with development pressure and that retrospective hotspot mitigation can miss population decline; calls for forward regional movement planning."
    Source.publicAttribution)
  urbanMovementRisk
  southEastQueenslandRegionalEvidence
  "Road/development effects and movement mitigation must be evaluated dynamically in the surrounding landscape, not only from historical hotspots."
  "Supports including induced movement/road exposure and cumulative surrounding development in the likely-effect question where the local causal chain is established."
  "Supports considering whether loss of a remaining connection increases movement risk for the relevant viable population."
  "Regional evidence does not prove the local road-risk magnitude at Springview."

mcleanMovementStudy : ScienceSnowballEntry
mcleanMovementStudy = science-snowball-entry
  (Source.mkDOISource
    "Christopher M. McLean; Matthew A. Stanton; Rodney P. Kavanagh"
    "Home Range and Movement of the Koala (Phascolarctos cinereus) in Fragmented High-Quality Coastal Habitat"
    "Austral Ecology"
    "2025"
    "10.1111/aec.70108"
    "https://doi.org/10.1111/aec.70108"
    Source.academicArticleSource
    "GPS movement/home-range study in fragmented high-quality coastal habitat, showing strong local use of high-quality patches and variable movement/road-crossing behaviour."
    Source.publicAttribution)
  fragmentationMechanism
  peerReviewedGeneralMechanism
  "Fine-scale movement and home-range use can make high-quality habitat locally important even within a fragmented landscape; movement response is population/site dependent."
  "Supports seeking current local movement/use evidence instead of assuming that nearby habitat makes loss harmless."
  "Supports testing functional substitutability and bottleneck importance with local evidence."
  "The NSW study is mechanism/method evidence, not a Springview population estimate."

nationalKoalaMonitoringProgram : ScienceSnowballEntry
nationalKoalaMonitoringProgram = science-snowball-entry
  (Source.mkNoDOISource
    "Department of Climate Change, Energy, the Environment and Water; CSIRO"
    "National Koala Monitoring Program"
    "Australian Government national monitoring program"
    "2025"
    "https://www.dcceew.gov.au/environment/biodiversity/threatened/species/koalas/national-koala-monitoring-program"
    Source.governmentSource
    "Current national monitoring framework emphasising survey-design dependence, multi-source modelling and the need not to compare incompatible population estimates as if they were a single time series."
    Source.publicAttribution)
  habitatDefinitionAndSurvey
  officialGeneralGuidance
  "Population estimates depend on survey method and sampling design; improved detection can change estimates without representing biological population growth."
  "Supports explicit uncertainty and method provenance for any current local abundance/density evidence used in s 102."
  "Supports defining a population with compatible spatial/temporal evidence rather than inferring viability from isolated occurrence records."
  "National monitoring does not itself identify the local Woogaroo population."

------------------------------------------------------------------------
-- Source atlas and consumer summary.
------------------------------------------------------------------------

koalaScienceSourceAtlas : Source.AttributedSourceAtlas
koalaScienceSourceAtlas = Source.mkSourceAtlas
  "Woogaroo current koala science source atlas"
  "DASHI.Law.SensibLawWoogarooKoalaScienceSnowballExact"
  (source endangeredKoalaHabitatGuidance ∷
   source koalaRecoveryPlan ∷
   source koalaHabitatMethodsReview ∷
   source bruntonConnectivityReview ∷
   source frereSubdivisionStudy ∷
   source mclennanGenomicsStudy ∷
   source dexterSEQVehicleStrikeStudy ∷
   source mcleanMovementStudy ∷
   source nationalKoalaMonitoringProgram ∷ [])
  "Current official guidance plus peer-reviewed state-of-the-art science for habitat definition, connectivity, fragmentation, population genetics, urban movement risk and survey uncertainty. These sources support methods/mechanisms only unless separately joined to Springview/Woogaroo same-object data."

record ConsumerScienceState : Set where
  constructor consumer-science-state
  field
    s102MechanismLiteraturePaid : Bool
    s102CurrentLocalEffectOpinionPaid : Bool
    s13PopulationMethodLiteraturePaid : Bool
    s13LocalPopulationIdentityPaid : Bool
    s13LocalEssentialityCounterfactualPaid : Bool
    sameObjectScienceStillRequired : Bool

currentConsumerScienceState : ConsumerScienceState
currentConsumerScienceState = consumer-science-state
  true false true false false true

------------------------------------------------------------------------
-- WrongType / attribution boundaries.
------------------------------------------------------------------------

data GeneralScienceEqualsSameObjectEvidence : Set where
data RegionalSEQFindingEqualsSpringviewFinding : Set where
data ConnectivityMapEqualsFunctionalConnectivity : Set where
data LiteratureMechanismEqualsLikelyEffect : Set where
data GenomicRiskEqualsLocalPopulationIdentity : Set where
data MitigationExistsEqualsMitigationEffective : Set where

generalScienceDoesNotCreateSameObjectEvidence : GeneralScienceEqualsSameObjectEvidence → ⊥
generalScienceDoesNotCreateSameObjectEvidence ()

regionalFindingDoesNotBecomeSpringviewFinding : RegionalSEQFindingEqualsSpringviewFinding → ⊥
regionalFindingDoesNotBecomeSpringviewFinding ()

mapDoesNotBecomeFunctionalConnectivity : ConnectivityMapEqualsFunctionalConnectivity → ⊥
mapDoesNotBecomeFunctionalConnectivity ()

mechanismDoesNotBecomeLikelyEffect : LiteratureMechanismEqualsLikelyEffect → ⊥
mechanismDoesNotBecomeLikelyEffect ()

genomicRiskDoesNotIdentifyLocalPopulation : GenomicRiskEqualsLocalPopulationIdentity → ⊥
genomicRiskDoesNotIdentifyLocalPopulation ()

mitigationExistenceDoesNotProveEffectiveness : MitigationExistsEqualsMitigationEffective → ⊥
mitigationExistenceDoesNotProveEffectiveness ()
