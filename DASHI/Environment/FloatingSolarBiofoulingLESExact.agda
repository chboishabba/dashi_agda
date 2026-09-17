module DASHI.Environment.FloatingSolarBiofoulingLESExact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Core.ScientificWorkAttributionExact as Attribution

------------------------------------------------------------------------
-- FLOATING SOLAR / BIOFOULING / OYSTER / IMTA LES OWNER
--
-- External studies are retained as external scientific sources.  DASHI owns
-- only the formal decomposition and finite collision witnesses below.
--
-- Core separations:
--
--   artificial substrate != realised colonisation
--   larval supply != successful recruitment
--   colonisation != net ecological benefit
--   filtration != net nutrient removal
--   local taxon richness != whole-system intervention value
--   pilot/demonstrator observation != commercial-scale outcome
--   habitat creation != benign landscape connectivity
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Source atlas.
------------------------------------------------------------------------

record FloatingSolarAttributedSource : Set where
  constructor floating-solar-attributed-source
  field
    authors : String
    title : String
    publication : String
    year : Nat
    stableIdentifier : String
    boundedClaim : String
    excludedPromotion : String
    sourceStrength : Attribution.SourceStrength
    claimOwner : Attribution.ClaimOwner
    ownerRemainsExternal : claimOwner ≡ Attribution.externalSourceOwner

open FloatingSolarAttributedSource public

mavrakiEtAl2025DOI : String
mavrakiEtAl2025DOI = "10.1016/j.seares.2025.102627"

mavrakiObservedTaxa : Nat
mavrakiObservedTaxa = 47

mavrakiObservedNISTaxa : Nat
mavrakiObservedNISTaxa = 12

mavrakiEtAl2025 : FloatingSolarAttributedSource
mavrakiEtAl2025 = floating-solar-attributed-source
  "Ninon Mavraki; Oscar G. Bos; Babeth van der Weide; Oliver Bittner; Brigitte M. Vlaswinkel; Melina Nalmpanti; Joop W. P. Coolen"
  "Inventory of the biofouling community on the first offshore solar energy farm in the North Sea"
  "Journal of Sea Research 208 (2025) 102627"
  2025
  "DOI 10.1016/j.seares.2025.102627"
  "Quantitative scraping of biofouling from underwater portions of 18 floaters in three clusters at the first Dutch offshore solar farm identified 47 taxa including 12 non-indigenous taxa; Arthropoda dominated abundance and Mytilus edulis dominated biomass. The paper states that offshore solar structures could act as stepping stones and calls for longer-term monitoring."
  "One young installation does not establish net biodiversity benefit, long-term benthic outcome, commercial-farm scaling, nutrient-removal magnitude, oyster-restoration success, or deployment authority."
  Attribution.primaryPublicationRecord Attribution.externalSourceOwner refl

terHofstedeVanKoningsveld2024 : FloatingSolarAttributedSource
terHofstedeVanKoningsveld2024 = floating-solar-attributed-source
  "Remment ter Hofstede; Mark van Koningsveld"
  "Defining operational objectives for nature-inclusive marine infrastructure to achieve system-scale impact"
  "Frontiers in Marine Science 11:1358851"
  2024
  "DOI 10.3389/fmars.2024.1358851"
  "Nature-inclusive marine infrastructure can be given explicit operational objectives; for European flat oyster restoration the paper discusses active introduction toward an initial critical mass together with suitable habitat."
  "A system-scale planning framework does not prove that any particular floating-solar site can sustain oysters, that seeding is locally safe, or that restoration objectives equal aquaculture objectives."
  Attribution.primaryPublicationRecord Attribution.externalSourceOwner refl

hydrodynamicSettlement2025 : FloatingSolarAttributedSource
hydrodynamicSettlement2025 = floating-solar-attributed-source
  "Ecological Engineering shellfish-settlement study authors"
  "Substrate-mediated alterations to hydrodynamic conditions enhances shellfish larval settlement: Implications for artificial reef restoration"
  "Ecological Engineering 212 (2025) 107474"
  2025
  "DOI 10.1016/j.ecoleng.2024.107474"
  "Increasing substrate roughness and structural complexity increased shellfish larval settlement and enlarged low-velocity regions in the tested restoration substrates."
  "A settlement-substrate experiment does not establish sufficient larval supply, adult persistence, site carrying capacity, net ecological benefit, or transferability to an offshore-solar design without a site-specific adapter."
  Attribution.primaryPublicationRecord Attribution.externalSourceOwner refl

flatOysterSubstrate2024 : FloatingSolarAttributedSource
flatOysterSubstrate2024 = floating-solar-attributed-source
  "Ecological Engineering European flat-oyster substrate study authors"
  "Settlement success of European flat oyster (Ostrea edulis) on different types of hard substrate to support reef development in offshore wind farms"
  "Ecological Engineering 200 (2024) 107189"
  2024
  "DOI 10.1016/j.ecoleng.2024.107189"
  "European flat-oyster larval settlement differed among hard-substrate types; suitable substrate can support reef-development objectives around offshore infrastructure."
  "Substrate preference does not create larvae, eliminate disease or biosecurity constraints, prove self-sustaining recruitment, or establish a floating-solar engineering prescription."
  Attribution.primaryPublicationRecord Attribution.externalSourceOwner refl

novelFlatOysterSubstrate2025 : FloatingSolarAttributedSource
novelFlatOysterSubstrate2025 = floating-solar-attributed-source
  "Ecological Engineering European flat-oyster settlement-substrate study authors"
  "Novel settlement substrates for European flat oyster (Ostrea edulis) restoration"
  "Ecological Engineering 212 (2025) 107532"
  2025
  "DOI 10.1016/j.ecoleng.2025.107532"
  "Hatchery and field tests found that settlement success can be altered by purpose-designed substrate composition and geometry."
  "Improved spat settlement does not by itself establish reef persistence, ecosystem-service magnitude, commercial feasibility, or deployment authority."
  Attribution.primaryPublicationRecord Attribution.externalSourceOwner refl

------------------------------------------------------------------------
-- Habitat opportunity is joint.  No single favourable marginal is treated as
-- sufficient for establishment.
------------------------------------------------------------------------

record HabitatOpportunity : Set where
  constructor habitat-opportunity
  field
    suitableSubstrate : Bool
    larvalSupply : Bool
    hydrodynamicSuitability : Bool
    postSettlementPersistence : Bool
    connectivitySupportsRecruitment : Bool

open HabitatOpportunity public

data ReefEstablishmentWorld : Set where
  substrateButNoLarvae
  substrateAndLarvae
  larvaeButNoSubstrate : ReefEstablishmentWorld

substrateProjection : ReefEstablishmentWorld → Bool
substrateProjection substrateButNoLarvae = true
substrateProjection substrateAndLarvae = true
substrateProjection larvaeButNoSubstrate = false

larvalSupplyProjection : ReefEstablishmentWorld → Bool
larvalSupplyProjection substrateButNoLarvae = false
larvalSupplyProjection substrateAndLarvae = true
larvalSupplyProjection larvaeButNoSubstrate = true

reefEstablished : ReefEstablishmentWorld → Bool
reefEstablished substrateButNoLarvae = false
reefEstablished substrateAndLarvae = true
reefEstablished larvaeButNoSubstrate = false

substrateEstablishmentDiffers :
  reefEstablished substrateButNoLarvae ≡ reefEstablished substrateAndLarvae → ⊥
substrateEstablishmentDiffers ()

larvalEstablishmentDiffers :
  reefEstablished substrateAndLarvae ≡ reefEstablished larvaeButNoSubstrate → ⊥
larvalEstablishmentDiffers ()

substrateNonFactorability :
  INF.NonFactorabilityWitness substrateProjection reefEstablished
substrateNonFactorability =
  INF.nonFactorabilityWitness
    substrateButNoLarvae substrateAndLarvae refl substrateEstablishmentDiffers

larvalSupplyNonFactorability :
  INF.NonFactorabilityWitness larvalSupplyProjection reefEstablished
larvalSupplyNonFactorability =
  INF.nonFactorabilityWitness
    substrateAndLarvae larvaeButNoSubstrate refl larvalEstablishmentDiffers

SubstrateFactorisation : Set₁
SubstrateFactorisation = INF.FactorsThrough substrateProjection reefEstablished

LarvalSupplyFactorisation : Set₁
LarvalSupplyFactorisation = INF.FactorsThrough larvalSupplyProjection reefEstablished

substrateAloneCannotDetermineReefEstablishment : SubstrateFactorisation → ⊥
substrateAloneCannotDetermineReefEstablishment =
  INF.witnessRulesOutEveryFlatFactorisation substrateNonFactorability

larvalSupplyAloneCannotDetermineReefEstablishment : LarvalSupplyFactorisation → ⊥
larvalSupplyAloneCannotDetermineReefEstablishment =
  INF.witnessRulesOutEveryFlatFactorisation larvalSupplyNonFactorability

------------------------------------------------------------------------
-- Filtration is a process rate, not the same object as net nutrient export or
-- net water-quality benefit.  Identical clearance can coexist with different
-- fates for captured material.
------------------------------------------------------------------------

data FilterFateWorld : Set where
  sameFiltrationLocalRemineralisation
  sameFiltrationHarvestExport : FilterFateWorld

filtrationProjection : FilterFateWorld → Nat
filtrationProjection sameFiltrationLocalRemineralisation = 20
filtrationProjection sameFiltrationHarvestExport = 20

netWaterQualityBenefit : FilterFateWorld → Bool
netWaterQualityBenefit sameFiltrationLocalRemineralisation = false
netWaterQualityBenefit sameFiltrationHarvestExport = true

filtrationBenefitDiffers :
  netWaterQualityBenefit sameFiltrationLocalRemineralisation ≡
  netWaterQualityBenefit sameFiltrationHarvestExport → ⊥
filtrationBenefitDiffers ()

filtrationNonFactorability :
  INF.NonFactorabilityWitness filtrationProjection netWaterQualityBenefit
filtrationNonFactorability =
  INF.nonFactorabilityWitness
    sameFiltrationLocalRemineralisation
    sameFiltrationHarvestExport
    refl
    filtrationBenefitDiffers

FiltrationFactorisation : Set₁
FiltrationFactorisation =
  INF.FactorsThrough filtrationProjection netWaterQualityBenefit

filtrationAloneCannotDetermineNetWaterQualityBenefit :
  FiltrationFactorisation → ⊥
filtrationAloneCannotDetermineNetWaterQualityBenefit =
  INF.witnessRulesOutEveryFlatFactorisation filtrationNonFactorability

------------------------------------------------------------------------
-- Local richness can collide while whole-system value differs through native
-- provenance, stepping-stone risk, disease/biosecurity, trophic balance,
-- oxygen/benthic loading, harvesting, and connectivity.
------------------------------------------------------------------------

data RichnessWorld : Set where
  sameRichnessNativeBalanced
  sameRichnessSteppingStoneRisk : RichnessWorld

localTaxonRichness : RichnessWorld → Nat
localTaxonRichness sameRichnessNativeBalanced = 47
localTaxonRichness sameRichnessSteppingStoneRisk = 47

wholeSystemInterventionValue : RichnessWorld → Bool
wholeSystemInterventionValue sameRichnessNativeBalanced = true
wholeSystemInterventionValue sameRichnessSteppingStoneRisk = false

richnessValueDiffers :
  wholeSystemInterventionValue sameRichnessNativeBalanced ≡
  wholeSystemInterventionValue sameRichnessSteppingStoneRisk → ⊥
richnessValueDiffers ()

richnessNonFactorability :
  INF.NonFactorabilityWitness localTaxonRichness wholeSystemInterventionValue
richnessNonFactorability =
  INF.nonFactorabilityWitness
    sameRichnessNativeBalanced sameRichnessSteppingStoneRisk refl richnessValueDiffers

LocalRichnessFactorisation : Set₁
LocalRichnessFactorisation =
  INF.FactorsThrough localTaxonRichness wholeSystemInterventionValue

localRichnessAloneCannotDetermineWholeSystemValue :
  LocalRichnessFactorisation → ⊥
localRichnessAloneCannotDetermineWholeSystemValue =
  INF.witnessRulesOutEveryFlatFactorisation richnessNonFactorability

------------------------------------------------------------------------
-- Multi-trophic planning surface.  These are planning coordinates only: the
-- owner does not claim any particular site supports all guilds simultaneously.
------------------------------------------------------------------------

data TrophicFunction : Set where
  suspensionFeederFiltration
  dissolvedNutrientAssimilation
  habitatEngineering
  harvestNutrientExport
  benthicMicrobialProcessing : TrophicFunction

record MultiTrophicCandidate : Set where
  constructor multi-trophic-candidate
  field
    bivalveLanePresent : Bool
    macroalgalLanePresent : Bool
    benthicProcessingObserved : Bool
    harvestExportPlanned : Bool
    oxygenConstraintChecked : Bool
    benthicLoadingConstraintChecked : Bool
    diseaseBiosecurityChecked : Bool
    nonIndigenousSpeciesRiskChecked : Bool
    hydrodynamicLoadChecked : Bool
    maintenanceInterferenceChecked : Bool

open MultiTrophicCandidate public

record TrophicSubstrateBoundary : Set where
  constructor trophic-substrate-boundary
  field
    maximiseOysterBiomassIsUniversalObjective : Bool
    filtrationEqualsNetNutrientRemoval : Bool
    localHabitatProvisionImpliesBenignConnectivity : Bool
    activeSeedingImpliesSelfSustainingReef : Bool
    restorationStockEqualsAquacultureStock : Bool
    renewableStructureCreatesDeploymentAuthority : Bool

canonicalTrophicSubstrateBoundary : TrophicSubstrateBoundary
canonicalTrophicSubstrateBoundary =
  trophic-substrate-boundary false false false false false false

------------------------------------------------------------------------
-- Explicit no-promotion propositions.
------------------------------------------------------------------------

data ColonisationImpliesNetEcologicalBenefit : Set where
data LocalTaxonRichnessImpliesWholeSystemValue : Set where
data DemonstratorImpliesCommercialScaleOutcome : Set where
data FiltrationEqualsNetNutrientExport : Set where
data HabitatProvisionImpliesBenignConnectivity : Set where
data SeedingImpliesSelfSustainingReef : Set where

colonisationDoesNotCreateNetBenefit : ColonisationImpliesNetEcologicalBenefit → ⊥
colonisationDoesNotCreateNetBenefit ()

localRichnessDoesNotCreateWholeSystemValue :
  LocalTaxonRichnessImpliesWholeSystemValue → ⊥
localRichnessDoesNotCreateWholeSystemValue ()

demonstratorDoesNotCreateCommercialScaleOutcome :
  DemonstratorImpliesCommercialScaleOutcome → ⊥
demonstratorDoesNotCreateCommercialScaleOutcome ()

filtrationDoesNotEqualNetNutrientExport : FiltrationEqualsNetNutrientExport → ⊥
filtrationDoesNotEqualNetNutrientExport ()

habitatProvisionDoesNotCreateBenignConnectivity :
  HabitatProvisionImpliesBenignConnectivity → ⊥
habitatProvisionDoesNotCreateBenignConnectivity ()

seedingDoesNotCreateSelfSustainingReef : SeedingImpliesSelfSustainingReef → ⊥
seedingDoesNotCreateSelfSustainingReef ()

------------------------------------------------------------------------
-- Attribution/authority boundary.
------------------------------------------------------------------------

record FloatingSolarLESAuthorityBoundary : Set where
  constructor floating-solar-les-authority-boundary
  field
    sourceObservationEqualsDashiReconstruction : Bool
    sourceIdentifierCreatesScientificClaim : Bool
    settlementSuccessCreatesReefPersistence : Bool
    reefPersistenceCreatesNetWaterQualityBenefit : Bool
    localPilotCreatesCommercialScaleOutcome : Bool
    formalisationCreatesDeploymentAuthority : Bool

canonicalFloatingSolarLESAuthorityBoundary : FloatingSolarLESAuthorityBoundary
canonicalFloatingSolarLESAuthorityBoundary =
  floating-solar-les-authority-boundary false false false false false false

floatingSolarLESSummary : String
floatingSolarLESSummary =
  "Floating renewable infrastructure is treated as a controllable trophic substrate only through situated LES evidence: substrate, propagule supply, hydrodynamics, persistence, connectivity, material fate, native/NIS risk, oxygen/benthic loading, harvest and maintenance remain separate coordinates."
