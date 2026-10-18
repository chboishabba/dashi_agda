module DASHI.Biology.Agriculture.AustralianTopsoilPropaguleBiotaCarrierExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Attribution

golosEtAl2016DOI : String
golosEtAl2016DOI = "10.1111/rec.12389"

valliereEtAl2022DOI : String
valliereEtAl2022DOI = "10.1007/s11104-021-05217-z"

golosEtAl2016 : Attribution.AttributedSource
golosEtAl2016 = Attribution.mkDOISource
  "Peter J. Golos; Kingsley W. Dixon; Todd E. Erickson"
  "Plant recruitment from the soil seed bank depends on topsoil stockpile age, height, and storage history in an arid environment"
  "Restoration Ecology 24(S2):S53-S61"
  "2016" golosEtAl2016DOI "https://doi.org/10.1111/rec.12389"
  Attribution.academicArticleSource
  "Pilbara arid-zone mine-rehabilitation source comparing fresh topsoil with one- and three-year stockpiles and top/bottom stockpile positions. Total emergence, perennial recruitment and Triodia emergence responded differently to stockpile age/depth/history, so topsoil restoration value remains consumer- and handling-context indexed."
  Attribution.publicAttribution

valliereEtAl2022 : Attribution.AttributedSource
valliereEtAl2022 = Attribution.mkDOISource
  "Justin M. Valliere; Haylee M. D'Agui; Kingsley W. Dixon; Paul G. Nevill; Wei San Wong; Hongtao Zhong; Erik J. Veneklaas; et al."
  "Stockpiling disrupts the biological integrity of topsoil for ecological restoration"
  "Plant and Soil 471:409-426"
  "2022" valliereEtAl2022DOI "https://doi.org/10.1007/s11104-021-05217-z"
  Attribution.academicArticleSource
  "Six-mine-site Western Australian Acacia phytometer experiment comparing native-reference and stockpiled topsoils. Plants in stockpiled soils generally had lower biomass, fewer N-fixing root nodules and lower water-use efficiency while measured soil physicochemistry showed relatively few/minor differences, supporting a biological-integrity loss not reducible to the measured abiotic panel."
  Attribution.publicAttribution

data TopsoilCarrierRole : Set where
  propaguleSeedBankCarrier : TopsoilCarrierRole
  soilBiotaCarrier : TopsoilCarrierRole
  symbiontCapacityCarrier : TopsoilCarrierRole
  edaphicResourceCarrier : TopsoilCarrierRole
  plantPerformanceMedium : TopsoilCarrierRole

data TopsoilConsumer : Set where
  totalSeedlingRecruitmentConsumer : TopsoilConsumer
  perennialRecruitmentConsumer : TopsoilConsumer
  triodiaRecruitmentConsumer : TopsoilConsumer
  acaciaBiomassConsumer : TopsoilConsumer
  acaciaNodulationConsumer : TopsoilConsumer
  acaciaWUEConsumer : TopsoilConsumer

record TopsoilCarrierBoundary : Set where
  constructor topsoil-carrier-boundary
  field
    stockpileAgeAloneDeterminesPropaguleRecruitment : Bool
    totalSeedlingEmergenceDeterminesPerennialRecruitment : Bool
    seedBankConditionDeterminesRhizobialNodulationCapacity : Bool
    similarMeasuredPhysicochemistryImpliesSimilarBiologicalIntegrity : Bool
    onePlantBioassayDeterminesWholeCommunityRestorationValue : Bool
    stockpileDepthAgeHandlingAndOriginMustRemainIndexed : Bool
    restorationConsumerMustRemainIndexed : Bool
    directTransferBenefitCreatesUniversalTopsoilPrescription : Bool
    topsoilCarrierReceiptCreatesDeploymentAuthority : Bool
open TopsoilCarrierBoundary public

canonicalTopsoilCarrierBoundary : TopsoilCarrierBoundary
canonicalTopsoilCarrierBoundary = topsoil-carrier-boundary
  false false false false false true true false false

attributionRule : String
attributionRule =
  "Golos, Dixon & Erickson 2016 (DOI 10.1111/rec.12389) owns its Pilbara topsoil-stockpile age/depth/history and seedling-recruitment observations. Valliere et al. 2022 (DOI 10.1007/s11104-021-05217-z) owns its six-site Western Australian native-reference/stockpiled-topsoil Acacia biomass, physiology and N-fixing-nodulation observations. DASHI owns only the typed multi-carrier interpretation and no-promotion boundary. Seed-bank recruitment, rhizobial nodulation capacity, measured physicochemistry and whole-community restoration value remain separate consumers; direct-transfer benefit does not create universal deployment authority."
