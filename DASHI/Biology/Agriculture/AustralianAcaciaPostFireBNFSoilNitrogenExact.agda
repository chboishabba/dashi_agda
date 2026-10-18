module DASHI.Biology.Agriculture.AustralianAcaciaPostFireBNFSoilNitrogenExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Biology.Agriculture.NitrogenaseChemistryCrossPollinationExact as Chemistry

------------------------------------------------------------------------
-- AUSTRALIAN ACACIA POST-FIRE BNF <-> SOIL MINERAL-N TRAJECTORY
--
-- Same-object Brisbane experiment joining prescribed-fire history, native
-- Acacia species, foliar natural-abundance 15N/Ndfa, soil mineral N and
-- biochar treatment through the first post-fire years.  The owner preserves
-- the measurement hierarchy: Ndfa is not direct fixation flux, and mineral-N
-- response is not identified with BNF contribution alone.
------------------------------------------------------------------------

liEtAl2024DOI : String
liEtAl2024DOI = "10.1007/s11368-024-03816-8"

liEtAl2024 : Attribution.AttributedSource
liEtAl2024 = Attribution.mkDOISource
  "Jing Li; Zhihong Xu; Chengrong Chen; et al."
  "Long-term effects of biochar application on biological nitrogen fixation of acacia species and soil carbon and nitrogen pools in an Australian subtropical native forest"
  "Journal of Soils and Sediments"
  "2024"
  liEtAl2024DOI
  "https://doi.org/10.1007/s11368-024-03816-8"
  Attribution.academicArticleSource
  "Toohey Forest, Brisbane, Queensland post-fire field experiment following Acacia leiocalyx and Acacia disparimma through the first 4-5 years after prescribed burning and approximately 3.5 years of biochar treatment. Foliar natural-abundance 15N/Ndfa, plant growth, soil NH4-N/NO3-N and soil C/N pools were observed across biochar rates. Atmospheric N deposition, rainfall/soil-moisture history, species identity and biochar treatment remain explicit; foliar Ndfa is not relabelled as a direct fixed-N flux measurement."
  Attribution.publicAttribution

------------------------------------------------------------------------
-- Source-bounded joined receipt.
------------------------------------------------------------------------

data PostFireBNFEvidenceRole : Set where
  postFirePlantBNFProxy : PostFireBNFEvidenceRole
  postFireSoilMineralNitrogen : PostFireBNFEvidenceRole
  biocharPlantSoilInteraction : PostFireBNFEvidenceRole

record PostFireBNFReceipt : Set where
  constructor post-fire-bnf-receipt
  field
    source : Attribution.AttributedSource
    sourceDOI : String
    role : PostFireBNFEvidenceRole
    speciesReading : String
    disturbanceReading : String
    treatmentReading : String
    plantMeasurementReading : String
    soilMeasurementReading : String
    boundedReading : String
open PostFireBNFReceipt public

plantBNFReceipt : PostFireBNFReceipt
plantBNFReceipt = post-fire-bnf-receipt
  liEtAl2024
  liEtAl2024DOI
  postFirePlantBNFProxy
  "Acacia leiocalyx and Acacia disparimma retained separately"
  "prescribed burn in 2017 with 4-5 year post-fire observation window"
  "biochar 0, 5 and 10 t/ha"
  "growth, foliar total N, delta-15N and natural-abundance Ndfa estimates"
  "soil mineral-N and C/N state measured separately"
  "high Ndfa is plant-level isotope evidence, not a direct whole-plant or ecosystem fixed-N flux receipt"

soilMineralNReceipt : PostFireBNFReceipt
soilMineralNReceipt = post-fire-bnf-receipt
  liEtAl2024
  liEtAl2024DOI
  postFireSoilMineralNitrogen
  "same native Acacia post-fire plots"
  "post-fire recovery under variable rainfall and atmospheric-N context"
  "biochar rates retained"
  "Acacia growth and foliar isotope state"
  "NH4-N, NO3-N and associated soil C/N pools"
  "mineral-N differences cannot be assigned to BNF alone because nitrification/mineralisation, deposition, leaching, plant uptake and moisture context remain live"

biocharInteractionReceipt : PostFireBNFReceipt
biocharInteractionReceipt = post-fire-bnf-receipt
  liEtAl2024
  liEtAl2024DOI
  biocharPlantSoilInteraction
  "Acacia leiocalyx and Acacia disparimma"
  "multi-year recovery after prescribed fire"
  "biochar treatment crossed with species and time"
  "growth and foliar Ndfa proxy"
  "soil mineral-N retention/loss and C/N pools"
  "biochar effects on plant growth or nitrate retention are not identified with a BNF increase unless the fixation measurement itself supports that inference"

------------------------------------------------------------------------
-- Canonical BNF ladder remains authoritative.
------------------------------------------------------------------------

bacterialFixedNFluxStillOpen :
  Chemistry.stageClosed Chemistry.bacterialFixedNFlux ≡ false
bacterialFixedNFluxStillOpen = refl

seasonalPlantDemandStillOpen :
  Chemistry.stageClosed Chemistry.seasonalCropNDemand ≡ false
seasonalPlantDemandStillOpen = refl

------------------------------------------------------------------------
-- No-promotion boundary.
------------------------------------------------------------------------

record PostFireBNFBoundary : Set where
  constructor post-fire-bnf-boundary
  field
    foliarNdfaImpliesMeasuredFixedNFlux : Bool
    highNdfaImpliesRecoveredSoilNitrogenPool : Bool
    soilMineralNChangeAttributableToBNFAlone : Bool
    biocharGrowthResponseImpliesBNFIncrease : Bool
    biocharNitrateRetentionImpliesPlantNitrogenAssimilation : Bool
    prescribedFireHistoryMayBeDropped : Bool
    atmosphericNitrogenDepositionMayBeDropped : Bool
    extremeRainfallAndSoilMoistureMayBeDropped : Bool
    acaciaSpeciesIdentityMayBeDropped : Bool
    mineralNitrogenRetentionImpliesSeasonalPlantDemandPaid : Bool
    australianAcaciaEvidenceClosesSenegaliaBacterialFixedNFlux : Bool
    postFireFieldEvidenceCreatesFertilizerSubstitutionReceipt : Bool
open PostFireBNFBoundary public

canonicalPostFireBNFBoundary : PostFireBNFBoundary
canonicalPostFireBNFBoundary = post-fire-bnf-boundary
  false false false false false false false false false false false false

attributionRule : String
attributionRule =
  "Li et al. 2024 (DOI 10.1007/s11368-024-03816-8) owns its Toohey-Forest post-fire Acacia leiocalyx/Acacia disparimma, biochar, foliar natural-abundance 15N/Ndfa, growth and soil C/mineral-N propositions. DASHI owns only the typed joined receipt and no-promotion boundary. Foliar Ndfa is not relabelled as direct fixation flux; soil NH4/NO3 dynamics are not assigned to BNF alone; biochar growth/mineral-N effects are not relabelled as fixation effects; and this Australian native-Acacia evidence does not close the Senegalia bacterial-fixed-N-flux, seasonal-demand or avoided-mineral-N stages."
