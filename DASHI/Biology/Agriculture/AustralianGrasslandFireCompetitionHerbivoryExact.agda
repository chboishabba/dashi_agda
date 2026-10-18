module DASHI.Biology.Agriculture.AustralianGrasslandFireCompetitionHerbivoryExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Environment.LESResearchCrossPollinationExact as LES
import DASHI.Biology.Agriculture.AustralianGrasslandSuccessionRegenerationExact as Grassland
import DASHI.Biology.Agriculture.AustralianAcaciaPioneerDisturbanceTrajectoryExact as Pioneer

------------------------------------------------------------------------
-- AUSTRALIAN GRASSLAND / ACACIA DISTURBANCE INTERACTION FIBRE
------------------------------------------------------------------------

butlerFairfax2003DOI : String
butlerFairfax2003DOI = "10.1046/j.1442-8903.2003.00146.x"

bellEtAl2022DOI : String
bellEtAl2022DOI = "10.1111/1365-2664.14192"

frenchEtAl2024DOI : String
frenchEtAl2024DOI = "10.1002/2688-8319.12355"

rigbyEtAl2026DOI : String
rigbyEtAl2026DOI = "10.1111/aec.70211"

butlerFairfax2003 : Attribution.AttributedSource
butlerFairfax2003 = Attribution.mkDOISource
  "Don W. Butler; Russell J. Fairfax"
  "Buffel Grass and fire in a Gidgee and Brigalow woodland: A case study from central Queensland"
  "Ecological Management & Restoration 4(2):120-125"
  "2003" butlerFairfax2003DOI "https://doi.org/10.1046/j.1442-8903.2003.00146.x"
  Attribution.academicArticleSource
  "Central Queensland Acacia cambagei / Acacia harpophylla woodland case study infested by Cenchrus ciliaris. Fifteen months after fire, burnt areas had lower living-tree basal area and higher Buffel Grass and Parthenium cover than unburnt areas, supporting an exotic-grass fuel / fire positive-feedback interpretation. The case study is retained as context-specific disturbance-feedback evidence, not a universal fire law."
  Attribution.publicAttribution

bellEtAl2022 : Attribution.AttributedSource
bellEtAl2022 = Attribution.mkDOISource
  "Kristian Bell; Tim S. Doherty; Tricia Wevill; Don A. Driscoll"
  "Restoration of a declining foundation plant species: Testing the roles of competitor suppression, fire reintroduction and herbivore exclusion"
  "Journal of Applied Ecology"
  "2022" bellEtAl2022DOI "https://doi.org/10.1111/1365-2664.14192"
  Attribution.academicArticleSource
  "Australian agricultural-landscape experiment on Triodia scariosa recruitment. Fire alone did not yield immediate recruitment; recruitment emerged by the second year and was greatest where fire and grass-competitor removal were combined, while herbivore exclusion/reserve context affected recovery toward original abundance. Seed-bank limitation and timing remain explicit."
  Attribution.publicAttribution

frenchEtAl2024 : Attribution.AttributedSource
frenchEtAl2024 = Attribution.mkDOISource
  "Ben J. French; Lynda D. Prior; Christopher N. Johnson; Steven W. J. Leonard; David M. J. S. Bowman"
  "Restoring landscape burning is compatible with conservation and livestock production in a southeast Australian grassland fragment"
  "Ecological Solutions and Evidence 5:e12355"
  "2024" frenchEtAl2024DOI "https://doi.org/10.1002/2688-8319.12355"
  Attribution.academicArticleSource
  "Tasmanian lowland grassland/woodland experiment crossing low-intensity burning with ambient/excluded herbivory. Fire and grazing effects differed among grassy sward and Poa tussock contexts; excluding herbivores increased exotic grass cover. Herbivory is therefore not represented as uniformly degrading and fire-grazing interaction remains vegetation-context dependent."
  Attribution.publicAttribution

rigbyEtAl2026 : Attribution.AttributedSource
rigbyEtAl2026 = Attribution.mkDOISource
  "Laura C. Rigby; Isabelle Hally; Catherine Leigh; A. Mark Osborn; Akane Uesugi"
  "The Effectiveness of Prescribed Fire for Native Grassland Restoration and Exotic Weed Control Differs Between Soil Types"
  "Austral Ecology 51(4):e70211"
  "2026" rigbyEtAl2026DOI "https://doi.org/10.1111/aec.70211"
  Attribution.academicArticleSource
  "Victorian temperate-grassland prescribed-fire experiment spanning nutrient-poor red and nutrient-rich grey soils. Fire reduced exotic cover on red soil but maintained exotic dominance and reduced native grass/forb abundance on grey soil; soil type, nutrients, invasion state and fire remain jointly indexed."
  Attribution.publicAttribution

data DisturbanceAxis : Set where
  prescribedFire : DisturbanceAxis
  competitorRemoval : DisturbanceAxis
  ambientHerbivory : DisturbanceAxis
  herbivoreExclusion : DisturbanceAxis
  exoticFuelLoad : DisturbanceAxis

data DisturbanceConsumer : Set where
  nativeRecruitmentConsumer : DisturbanceConsumer
  nativeAbundanceConsumer : DisturbanceConsumer
  exoticCoverConsumer : DisturbanceConsumer
  treeBasalAreaConsumer : DisturbanceConsumer
  communityCompositionConsumer : DisturbanceConsumer
  herbaceousBiomassConsumer : DisturbanceConsumer

record DisturbanceReceipt : Set where
  constructor disturbance-receipt
  field
    source : Attribution.AttributedSource
    sourceDOI : String
    temporalReading : String
    vegetationReading : String
    interactionReading : String
    boundedReading : String
open DisturbanceReceipt public

buffelFireFeedbackReceipt : DisturbanceReceipt
buffelFireFeedbackReceipt = disturbance-receipt
  butlerFairfax2003 butlerFairfax2003DOI
  "post-fire observation at fifteen months"
  "Gidgee/Brigalow Acacia woodland invaded by Buffel Grass"
  "fire crossed with existing exotic fuel/invasion state"
  "supports a context-specific positive feedback between Buffel Grass and fire; does not imply every grassland fire increases exotic cover"

triodiaRecruitmentReceipt : DisturbanceReceipt
triodiaRecruitmentReceipt = disturbance-receipt
  bellEtAl2022 bellEtAl2022DOI
  "before/after experiment with one- and two-year recruitment observations"
  "declining Triodia scariosa foundation-grass remnants"
  "fire crossed with competitor removal and herbivore context"
  "recruitment bottlenecks, delayed germination and herbivore/competition state prevent fire-only promotion"

fireHerbivoryReceipt : DisturbanceReceipt
fireHerbivoryReceipt = disturbance-receipt
  frenchEtAl2024 frenchEtAl2024DOI
  "two-year monitoring after low-intensity experimental burns"
  "Tasmanian lowland grassland and Poa-tussock patches"
  "burn treatment crossed with herbivore exclusion/ambient grazing"
  "grazing can suppress exotic grasses in this system and does not reduce to a universally negative conservation pressure"

soilSpecificFireReceipt : DisturbanceReceipt
soilSpecificFireReceipt = disturbance-receipt
  rigbyEtAl2026 rigbyEtAl2026DOI
  "post-prescribed-fire community response"
  "temperate grassland on nutrient-poor red versus nutrient-rich grey soil"
  "fire crossed with soil type, soil nutrients, invasion state and weed removal"
  "same nominal fire treatment produces different native/exotic community outcomes across soil contexts"

------------------------------------------------------------------------
-- Finite information-loss witness: fire identity cannot determine recovery.
------------------------------------------------------------------------

data FireWorld : Set where
  fireOnRedLowNutrientSoil : FireWorld
  fireOnGreyHighNutrientSoil : FireWorld

data FireToken : Set where
  prescribedFireToken : FireToken

data FireTask : Set where
  nativeRecoveryTask : FireTask

fireTreatmentOnly : FireWorld → FireToken
fireTreatmentOnly _ = prescribedFireToken

nativeRecovery : FireTask → FireWorld → Bool
nativeRecovery nativeRecoveryTask fireOnRedLowNutrientSoil = true
nativeRecovery nativeRecoveryTask fireOnGreyHighNutrientSoil = false

trueNotFalse : true ≡ false → ⊥
trueNotFalse ()

fireTreatmentNotTaskSufficient :
  LES.TaskFactorisation fireTreatmentOnly nativeRecovery → ⊥
fireTreatmentNotTaskSufficient factor =
  trueNotFalse
    (LES.sameRepresentationSameTaskOutput
      factor nativeRecoveryTask
      {fireOnRedLowNutrientSoil} {fireOnGreyHighNutrientSoil} refl)

------------------------------------------------------------------------
-- Existing trajectory owners reused without source fusion.
------------------------------------------------------------------------

grasslandBoundaryReused : Grassland.GrasslandSuccessionBoundary
grasslandBoundaryReused = Grassland.canonicalGrasslandBoundary

pioneerBoundaryReused : Pioneer.PioneerDisturbanceBoundary
pioneerBoundaryReused = Pioneer.canonicalPioneerDisturbanceBoundary

record DisturbanceBoundary : Set where
  constructor disturbance-boundary
  field
    fireTreatmentAloneDeterminesNativeRecovery : Bool
    sameFireTreatmentAcrossSoilsImpliesSameNativeResponse : Bool
    soilTypeAndNutrientContextMustRemainIndexed : Bool
    exoticGrassFuelFeedbackMayBeDropped : Bool
    exoticCompetitionMayBeDropped : Bool
    fireAloneOvercomesSeedBankAndRecruitmentLimitation : Bool
    fireBenefitHasOneSignAcrossLifeStages : Bool
    herbivoreStateMayBeDropped : Bool
    herbivoryAlwaysReducesConservationOutcome : Bool
    prescribedFireCreatesReferenceCommunityRecovery : Bool
    disturbanceResultCreatesUniversalManagementPrescription : Bool
    disturbanceResultCreatesDeploymentAuthority : Bool
    syntheticFireWorldsAreSourceMeasurements : Bool
open DisturbanceBoundary public

canonicalDisturbanceBoundary : DisturbanceBoundary
canonicalDisturbanceBoundary = disturbance-boundary
  false false true false false false false false false false false false false

attributionRule : String
attributionRule =
  "Butler & Fairfax 2003 (DOI 10.1046/j.1442-8903.2003.00146.x) owns its central-Queensland Gidgee/Brigalow-Buffel-fire case-study observations. Bell et al. 2022 (DOI 10.1111/1365-2664.14192) owns its Triodia fire/competitor/herbivore recruitment experiment. French et al. 2024 (DOI 10.1002/2688-8319.12355) owns its Tasmanian fire-by-herbivory grassland observations. Rigby et al. 2026 (DOI 10.1111/aec.70211) owns its Victorian soil-specific prescribed-fire experiment. DASHI owns only the typed disturbance interaction, finite fire-only TaskFactorisation collision and no-promotion boundary. Fire, grazing, competitor removal, soil fertility, exotic fuel state and recruitment stage are not collapsed into a context-free management rule."
