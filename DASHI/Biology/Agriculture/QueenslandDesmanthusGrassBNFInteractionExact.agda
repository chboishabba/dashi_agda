module DASHI.Biology.Agriculture.QueenslandDesmanthusGrassBNFInteractionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Biology.Agriculture.NitrogenaseChemistryCrossPollinationExact as Chemistry

------------------------------------------------------------------------
-- QUEENSLAND DESMANTHUS <-> RHIZOBIUM <-> GRASS / SOIL-N INTERACTION
--
-- This owner preserves the important sign-changing interaction that a
-- companion grass is not merely a competitor.  In high-mineral-N states a
-- pure Desmanthus sward can suppress realised fixation, while companion
-- grass can draw down mineral N even as it competes for water/nutrients.
-- None of this creates a universal positive grass effect.
------------------------------------------------------------------------

date1991 : Attribution.AttributedSource
date1991 = Attribution.mkNoDOISource
  "R. A. Date"
  "Nitrogen fixation in Desmanthus: strain specificity of Rhizobium and responses to inoculation in acidic and alkaline soil"
  "Tropical Grasslands 25:47-55"
  "1991"
  "https://www.tropicalgrasslands.info/public/journals/4/Historic/Tropical%20Grasslands%20Journal%20archive/Abstracts/Vol_25_1991/Abs_25_01_91_pp47_55.html"
  Attribution.academicArticleSource
  "Queensland-oriented host-accession × Rhizobium-strain × soil-acidity screening. Forty-eight Desmanthus accessions and 17 strains generated multiple effectiveness groups, with larger accession/strain differences in acidic Gympie soil than alkaline Gayndah clay. No DOI is recorded by this atlas."
  Attribution.publicAttribution

bahnischEtAl1998 : Attribution.AttributedSource
bahnischEtAl1998 = Attribution.mkNoDOISource
  "G. A. Bahnisch; R. A. Date; N. J. Brandon; P. Pittaway"
  "Growth responses of Desmanthus virgatus to inoculation with Rhizobium strain CB3126. I. A pot trial with 8 clay soils from central and southern Queensland"
  "Tropical Grasslands 32:13-19"
  "1998"
  "https://www.tropicalgrasslands.info/public/journals/4/Historic/Tropical%20Grasslands%20Journal%20archive/PDFs/Vol_32_1998/Vol_32_01_98_pp13_19.pdf"
  Attribution.academicArticleSource
  "Glasshouse experiment across eight Queensland clay soils comparing uninoculated, CB3126-inoculated and inoculated-plus-N Desmanthus. Serology separated inoculum occupancy from indigenous-rhizobial nodulation and showed inoculation benefit depended on native population and soil context. No DOI is recorded by this atlas."
  Attribution.publicAttribution

brandonEtAl1998 : Attribution.AttributedSource
brandonEtAl1998 = Attribution.mkNoDOISource
  "N. J. Brandon; R. A. Date; R. L. Clem; B. A. Robertson; T. W. G. Graham"
  "Growth responses of Desmanthus virgatus to inoculation with Rhizobium strain CB3126. II. A field trial at 4 sites in south-east Queensland"
  "Tropical Grasslands 32:20-27"
  "1998"
  "https://era.dpi.qld.gov.au/id/eprint/12291/"
  Attribution.academicArticleSource
  "Three-year field trial at four south-east Queensland sites comparing uninoculated, CB3126-inoculated and inoculated-plus-N Desmanthus cultivars. Inoculum-strain nodule occupancy was measured serologically and plant N derived from fixation was estimated by natural abundance in years two and three. Ndfa ranged from zero in a highly fertile soil to high proportions in lower-fertility soils. Indigenous-rhizobial prevalence, soil N, drought-driven nodule turnover and soil moisture remained active coordinates. No DOI is recorded by this atlas."
  Attribution.publicAttribution

data DesmanthusEvidenceRole : Set where
  accessionStrainSpecificity : DesmanthusEvidenceRole
  potSoilOccupancyCompetition : DesmanthusEvidenceRole
  multiSiteFieldNodulationAndNdfa : DesmanthusEvidenceRole
  droughtNoduleTurnover : DesmanthusEvidenceRole
  companionGrassMineralNInteraction : DesmanthusEvidenceRole

record DesmanthusReceipt : Set where
  constructor desmanthus-receipt
  field
    source : Attribution.AttributedSource
    role : DesmanthusEvidenceRole
    hostReading : String
    rhizobialReading : String
    soilReading : String
    temporalReading : String
    boundedReading : String
open DesmanthusReceipt public

strainSpecificityReceipt : DesmanthusReceipt
strainSpecificityReceipt = desmanthus-receipt
  date1991 accessionStrainSpecificity
  "multiple Desmanthus species/accessions"
  "17 Rhizobium strains; effectiveness is host dependent"
  "acidic Gympie versus alkaline Gayndah soils"
  "controlled screening"
  "strain identity alone is not an effectiveness ranking independent of host accession and soil"

potOccupancyReceipt : DesmanthusReceipt
potOccupancyReceipt = desmanthus-receipt
  bahnischEtAl1998 potSoilOccupancyCompetition
  "D. virgatus cv. Marc"
  "CB3126 inoculum competing with indigenous soil rhizobia"
  "eight central/southern Queensland clay soils"
  "glasshouse pot experiment"
  "inoculation, realised nodule occupancy and growth response remain separate; pot evidence is not a field same-object receipt"

fieldNdfaReceipt : DesmanthusReceipt
fieldNdfaReceipt = desmanthus-receipt
  brandonEtAl1998 multiSiteFieldNodulationAndNdfa
  "D. virgatus cultivars Marc, Bayamo and Uman"
  "CB3126 occupancy measured against indigenous nodulators"
  "four south-east Queensland soils spanning fertility/native-rhizobia contexts"
  "three years; Ndfa estimated in years two and three"
  "high soil fertility can coexist with nodulation yet strongly suppress atmospheric-N contribution; occupancy does not identify Ndfa"

droughtTurnoverReceipt : DesmanthusReceipt
droughtTurnoverReceipt = desmanthus-receipt
  brandonEtAl1998 droughtNoduleTurnover
  "field Desmanthus cultivars"
  "effective strain must persist through periods without active nodules"
  "water status and fertility retained jointly"
  "nodule death after drought and reformation after improved moisture"
  "one-time nodule observation cannot stand in for season-long symbiosis state"

companionGrassInteractionReceipt : DesmanthusReceipt
companionGrassInteractionReceipt = desmanthus-receipt
  brandonEtAl1998 companionGrassMineralNInteraction
  "Desmanthus field interpretation"
  "rhizobial activity remains mineral-N sensitive"
  "high-N pure-sward context contrasted with observations motivating companion-grass consideration"
  "field interpretation across seasons"
  "grass interaction cannot be assigned a universal sign: competition for resources and mineral-N drawdown are distinct pathways"

------------------------------------------------------------------------
-- Canonical BNF ladder remains authoritative.
------------------------------------------------------------------------

genericReactionEnablementStillOpen : Chemistry.stageClosed Chemistry.reactionEnablement ≡ false
genericReactionEnablementStillOpen = refl

genericFixedNFluxStillOpen : Chemistry.stageClosed Chemistry.bacterialFixedNFlux ≡ false
genericFixedNFluxStillOpen = refl

record DesmanthusBoundary : Set where
  constructor desmanthus-boundary
  field
    inoculationImpliesHighInoculantNoduleOccupancy : Bool
    highInoculantNoduleOccupancyImpliesHighNdfa : Bool
    soilMineralNitrogenMayBeDroppedFromRealisedFixation : Bool
    indigenousRhizobialPopulationMayBeDropped : Bool
    droughtAndNoduleTurnoverMayBeDropped : Bool
    companionGrassEffectIsUniversallyNegative : Bool
    companionGrassEffectIsUniversallyPositive : Bool
    pureSwardFixationPredictsGrassMixtureFixation : Bool
    potResponseCreatesFieldSameObjectReceipt : Bool
    naturalAbundanceNdfaEqualsDirectBacterialFlux : Bool
    desmanthusEvidenceCreatesAcaciaSameObjectReceipt : Bool
    desmanthusEvidenceClosesAcaciaReactionEnablement : Bool
    desmanthusEvidenceCreatesDeploymentAuthority : Bool
open DesmanthusBoundary public

canonicalDesmanthusBoundary : DesmanthusBoundary
canonicalDesmanthusBoundary = desmanthus-boundary
  false false false false false false false false false false false false false

attributionRule : String
attributionRule =
  "Date 1991 (Tropical Grasslands 25:47-55; no DOI recorded by this atlas) owns its Desmanthus accession × Rhizobium-strain × acidic/alkaline-soil effectiveness propositions. Bahnisch, Date, Brandon & Pittaway 1998-I (Tropical Grasslands 32:13-19; no DOI recorded by this atlas) owns its eight-soil pot inoculation, indigenous-rhizobial competition and serological-occupancy observations. Brandon, Date, Clem, Robertson & Graham 1998-II (Tropical Grasslands 32:20-27; no DOI recorded by this atlas) owns its three-year four-site south-east Queensland inoculation, nodule-occupancy, natural-abundance Ndfa and drought/nodule-turnover observations. DASHI owns only the typed inoculation/occupancy/Ndfa/environment separation and the sign-indeterminate companion-grass interaction. Desmanthus evidence is not Acacia/Senegalia same-object evidence and does not close canonical reaction enablement or bacterial fixed-N flux."
