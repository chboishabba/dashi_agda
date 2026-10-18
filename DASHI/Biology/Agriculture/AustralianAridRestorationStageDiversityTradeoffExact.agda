module DASHI.Biology.Agriculture.AustralianAridRestorationStageDiversityTradeoffExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Attribution

batemanEtAl2019DOI : String
batemanEtAl2019DOI = "10.1016/j.jenvman.2019.04.022"

batemanEtAl2019PMID : String
batemanEtAl2019PMID = "30999267"

batemanEtAl2021DOI : String
batemanEtAl2021DOI = "10.1016/j.geoderma.2021.115001"

batemanEtAl2019 : Attribution.AttributedSource
batemanEtAl2019 = Attribution.mkDOISource
  "Amber M. Bateman; Todd E. Erickson; David J. Merritt; Miriam Muñoz-Rojas"
  "Inorganic soil amendments alter seedling performance of native plant species in post-mining arid zone rehabilitation"
  "Journal of Environmental Management 241:179-186"
  "2019" batemanEtAl2019DOI "https://doi.org/10.1016/j.jenvman.2019.04.022"
  Attribution.academicArticleSource
  "Pilbara glasshouse experiments crossing gypsum/urea amendment combinations, substrate and five native species across germination, emergence and six-month growth stages. Amendments could reduce emergence and increase mortality while higher doses improved later growth among survivors, so intervention sign is life-stage and species/substrate dependent."
  Attribution.publicAttribution

batemanEtAl2021 : Attribution.AttributedSource
batemanEtAl2021 = Attribution.mkDOISource
  "Amber M. Bateman; Todd E. Erickson; David J. Merritt; Erik J. Veneklaas; Miriam Muñoz-Rojas"
  "Native plant diversity is a stronger driver for soil quality than inorganic amendments in semi-arid post-mining rehabilitation"
  "Geoderma 394:115001"
  "2021" batemanEtAl2021DOI "https://doi.org/10.1016/j.geoderma.2021.115001"
  Attribution.academicArticleSource
  "Twenty-one-month Pilbara mesocosm experiment crossing mine substrates, inorganic amendments and plant-community mixtures. Amendment effects on soil N/EC were initially strong but largely attenuated after about a year; plant survival and microbial activity depended on plant-community diversity and substrate, so longer-term soil/plant function is not determined by amendment identity alone."
  Attribution.publicAttribution

data RestorationStage : Set where
  germinationStage : RestorationStage
  emergenceStage : RestorationStage
  juvenileGrowthStage : RestorationStage
  twentyOneMonthCommunityStage : RestorationStage

data RestorationConsumer : Set where
  recruitmentConsumer : RestorationConsumer
  survivorGrowthConsumer : RestorationConsumer
  plantSurvivalConsumer : RestorationConsumer
  soilNitrogenConsumer : RestorationConsumer
  microbialActivityConsumer : RestorationConsumer
  communityFunctionConsumer : RestorationConsumer

record StageDiversityBoundary : Set where
  constructor stage-diversity-boundary
  field
    improvedLaterGrowthImpliesImprovedInitialRecruitment : Bool
    amendmentBenefitHasOneSignAcrossLifeStages : Bool
    initialAmendmentSoilNIncreaseImpliesPersistentSoilNIncrease : Bool
    inorganicAmendmentAloneDeterminesLongerTermSoilFunction : Bool
    plantDiversityMayBeDroppedFromPlantSoilFeedback : Bool
    speciesIdentityMayBeDroppedFromAmendmentResponse : Bool
    lifeStageTimePlantDiversityAndSubstrateMustRemainIndexed : Bool
    diversePlantCommunityBenefitCreatesUniversalMixturePrescription : Bool
    amendmentReceiptCreatesDeploymentAuthority : Bool
open StageDiversityBoundary public

canonicalStageDiversityBoundary : StageDiversityBoundary
canonicalStageDiversityBoundary = stage-diversity-boundary
  false false false false false false true false false

attributionRule : String
attributionRule =
  "Bateman, Erickson, Merritt & Munoz-Rojas 2019 (DOI 10.1016/j.jenvman.2019.04.022; PMID 30999267) owns its Pilbara gypsum/urea, substrate, species and life-stage observations. Bateman et al. 2021 (DOI 10.1016/j.geoderma.2021.115001) owns its 21-month Pilbara substrate/amendment/plant-diversity observations. DASHI owns only the typed stage/consumer separation and no-promotion boundary. A treatment that improves later survivor growth is not promoted to improved recruitment; transient soil-N change is not persistent functional recovery; plant-diversity benefit is not a universal mixture prescription or deployment authority."
