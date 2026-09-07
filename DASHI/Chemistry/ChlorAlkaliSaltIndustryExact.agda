module DASHI.Chemistry.ChlorAlkaliSaltIndustryExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Chemistry.TransitionKernel as Chemistry
open Chemistry
import DASHI.Geology.SaltGeochemistryExact as Salt

------------------------------------------------------------------------
-- CHLOR-ALKALI: GEOLOGICAL SALT -> BRINE -> CHLORINE / CAUSTIC / HYDROGEN
--
-- Source anchors:
--   O'Brien, Bommaraju & Hine (2005), Handbook of Chlor-Alkali Technology.
--   Euro Chlor, chlor-alkali process descriptions and membrane-cell practice.
--
-- This module formalises material identity, stoichiometric structure and
-- downstream application provenance.  It does not assert plant-specific cell
-- efficiencies, impurity tolerances, energy consumption, emissions or drinking
-- water dose requirements without an external application receipt.
------------------------------------------------------------------------

waterSpecies : Chemistry.Species
waterSpecies = record
  { speciesId = "water"
  ; phase = Chemistry.liquid
  ; chargeLabel = "0"
  ; compositionLabel = "H2O"
  ; mobilityClass = Chemistry.mobile
  ; activityModelLabel = "aqueous solvent model supplied by application"
  ; opticalRoleLabel = "not asserted"
  ; evidence = Chemistry.literatureEstablished
  }

chlorineGasSpecies : Chemistry.Species
chlorineGasSpecies = record
  { speciesId = "chlorine gas"
  ; phase = Chemistry.gas
  ; chargeLabel = "0"
  ; compositionLabel = "Cl2"
  ; mobilityClass = Chemistry.volatile
  ; activityModelLabel = "gas activity/fugacity model supplied by application"
  ; opticalRoleLabel = "not asserted"
  ; evidence = Chemistry.literatureEstablished
  }

hydrogenGasSpecies : Chemistry.Species
hydrogenGasSpecies = record
  { speciesId = "hydrogen gas"
  ; phase = Chemistry.gas
  ; chargeLabel = "0"
  ; compositionLabel = "H2"
  ; mobilityClass = Chemistry.volatile
  ; activityModelLabel = "gas activity/fugacity model supplied by application"
  ; opticalRoleLabel = "not asserted"
  ; evidence = Chemistry.literatureEstablished
  }

sodiumHydroxideSpecies : Chemistry.Species
sodiumHydroxideSpecies = record
  { speciesId = "sodium hydroxide in product liquor"
  ; phase = Chemistry.dissolved
  ; chargeLabel = "bulk neutral electrolyte/product representation"
  ; compositionLabel = "NaOH"
  ; mobilityClass = Chemistry.mobile
  ; activityModelLabel = "strong-electrolyte product model supplied by application"
  ; opticalRoleLabel = "not asserted"
  ; evidence = Chemistry.literatureEstablished
  }

------------------------------------------------------------------------
-- Literal overall stoichiometric transition:
--
--   2 NaCl + 2 H2O -> Cl2 + H2 + 2 NaOH
--
-- The actual electrochemical mechanism is electrode-separated and membrane /
-- diaphragm / legacy mercury-cell specific.  The overall transition therefore
-- does not erase half-reaction and separator obligations.
------------------------------------------------------------------------

chlorAlkaliRate : Chemistry.RateLaw
chlorAlkaliRate = record
  { rateLawKind = Chemistry.empirical
  ; symbolicForm = "electrolysis-controlled chlor-alkali rate supplied by plant model"
  ; parameters = []
  ; validityRegime = "purified brine and cell-specific electrochemical regime"
  ; evidence = Chemistry.literatureEstablished
  }

chlorAlkaliEnvironment : Chemistry.Environment
chlorAlkaliEnvironment = record
  { temperatureCarrier = "cell operating temperature supplied by plant receipt"
  ; pHCarrier = "anolyte/catholyte pH supplied by cell model"
  ; pressureCarrier = "cell/product pressure supplied by plant receipt"
  ; humidityCarrier = "not primary state variable"
  ; illuminationCarrier = "not primary state variable"
  ; ionicStrengthCarrier = "purified concentrated brine ionic-strength model"
  }

chlorAlkaliCondition : Chemistry.Condition
chlorAlkaliCondition = record
  { conditionLabel = "electrolytic chlor-alkali operation"
  ; environment = chlorAlkaliEnvironment
  ; guardExpression = "cell energised; brine purification and separator obligations satisfied"
  }

chlorAlkaliOverallTransition : Chemistry.Transition
chlorAlkaliOverallTransition = record
  { transitionId = "overall chlor-alkali electrolysis"
  ; transitionKind = Chemistry.chemicalReaction
  ; reactants =
      record { species = Salt.haliteSpecies ; coefficient = 2 }
      ∷ record { species = waterSpecies ; coefficient = 2 }
      ∷ []
  ; products =
      record { species = chlorineGasSpecies ; coefficient = 1 }
      ∷ record { species = hydrogenGasSpecies ; coefficient = 1 }
      ∷ record { species = sodiumHydroxideSpecies ; coefficient = 2 }
      ∷ []
  ; catalysts = []
  ; rateLaw = chlorAlkaliRate
  ; condition = chlorAlkaliCondition
  ; reversibility = Chemistry.irreversible
  ; evidence = Chemistry.literatureEstablished
  }

------------------------------------------------------------------------
-- Same-material weld from a geological salt lineage into the industrial cell.
------------------------------------------------------------------------

record ChlorAlkaliFeedWeld (lineage : Salt.SaltMaterialLineage) : Set₁ where
  constructor chlorAlkaliFeedWeld
  field
    feedBrine : Salt.BrineState
    feedBrineIsLineageBrine : feedBrine ≡ Salt.brine lineage

    sodiumFeedSpecies : Chemistry.Species
    chlorideFeedSpecies : Chemistry.Species

    sodiumFeedIsLineageSodium :
      sodiumFeedSpecies ≡ Salt.sodiumSpecies feedBrine
    chlorideFeedIsLineageChloride :
      chlorideFeedSpecies ≡ Salt.chlorideSpecies feedBrine

    brinePurificationReference : String
    anodeHalfReactionReference : String
    cathodeHalfReactionReference : String
    separatorOrMembraneReference : String
    sodiumAtomBalanceReference : String
    chlorineAtomBalanceReference : String
    hydrogenOxygenBalanceReference : String
    electronBalanceReference : String
    plantValidationReference : String

open ChlorAlkaliFeedWeld public

record ChlorAlkaliProductionReceipt (lineage : Salt.SaltMaterialLineage) : Set₁ where
  constructor chlorAlkaliProductionReceipt
  field
    feedWeld : ChlorAlkaliFeedWeld lineage
    overallTransition : Chemistry.Transition
    overallTransitionIsCanonical : overallTransition ≡ chlorAlkaliOverallTransition

    chlorineProduct : Chemistry.Species
    causticProduct : Chemistry.Species
    hydrogenProduct : Chemistry.Species

    chlorineIsCanonical : chlorineProduct ≡ chlorineGasSpecies
    causticIsCanonical : causticProduct ≡ sodiumHydroxideSpecies
    hydrogenIsCanonical : hydrogenProduct ≡ hydrogenGasSpecies

    sameChlorineAtomsFromGeologicalChlorideReference : String
    sameSodiumAtomsFromGeologicalSaltReference : String
    coproductMaterialLedgerReference : String
    energyInputReference : String
    cellTechnologyReference : String
    operatingEnvelopeReference : String
    empiricalProductionValidationReference : String

open ChlorAlkaliProductionReceipt public

------------------------------------------------------------------------
-- Downstream application graph.
-- Applications consume an actual production receipt; they do not manufacture
-- chlorine authority from a text label alone.
------------------------------------------------------------------------

data ChlorineApplicationKind : Set where
  drinkingWaterPrimaryDisinfection : ChlorineApplicationKind
  drinkingWaterSecondaryDisinfectantProduction : ChlorineApplicationKind
  sodiumHypochloriteProduction : ChlorineApplicationKind
  hydrochloricAcidProduction : ChlorineApplicationKind
  vinylChloridePVCChain : ChlorineApplicationKind
  pulpPaperBleachingChemistry : ChlorineApplicationKind
  industrialOxidationChlorination : ChlorineApplicationKind


data CausticApplicationKind : Set where
  waterTreatmentPHControl : CausticApplicationKind
  pulpPaperCausticProcessing : CausticApplicationKind
  soapDetergentChemistry : CausticApplicationKind
  aluminaProcessing : CausticApplicationKind
  generalIndustrialNeutralisation : CausticApplicationKind


record ChlorineApplicationReceipt
    {lineage : Salt.SaltMaterialLineage}
    (production : ChlorAlkaliProductionReceipt lineage) : Set₁ where
  constructor chlorineApplicationReceipt
  field
    application : ChlorineApplicationKind
    chlorineFeed : Chemistry.Species
    chlorineFeedIsProductionProduct :
      chlorineFeed ≡ chlorineProduct production
    downstreamNetwork : Chemistry.ReactionNetwork
    doseOrFeedRateReference : String
    transformationReference : String
    safetyControlReference : String
    regulationOrSpecificationReference : String
    monitoringReference : String
    validationReference : String

open ChlorineApplicationReceipt public

record CausticApplicationReceipt
    {lineage : Salt.SaltMaterialLineage}
    (production : ChlorAlkaliProductionReceipt lineage) : Set₁ where
  constructor causticApplicationReceipt
  field
    application : CausticApplicationKind
    causticFeed : Chemistry.Species
    causticFeedIsProductionProduct :
      causticFeed ≡ causticProduct production
    downstreamNetwork : Chemistry.ReactionNetwork
    doseOrFeedRateReference : String
    transformationReference : String
    safetyControlReference : String
    regulationOrSpecificationReference : String
    monitoringReference : String
    validationReference : String

open CausticApplicationReceipt public

------------------------------------------------------------------------
-- Tap-water provenance is a typed material lineage, not the claim that raw
-- halite itself is added to drinking water for disinfection.
------------------------------------------------------------------------

record DrinkingWaterChlorineLineage
    {lineage : Salt.SaltMaterialLineage}
    (production : ChlorAlkaliProductionReceipt lineage) : Set₁ where
  constructor drinkingWaterChlorineLineage
  field
    applicationReceipt : ChlorineApplicationReceipt production
    isPrimaryDisinfectionApplication :
      ChlorineApplicationReceipt.application applicationReceipt
      ≡ drinkingWaterPrimaryDisinfection
    sourceSaltReference : String
    chlorAlkaliPlantReference : String
    disinfectantPreparationReference : String
    treatmentPlantReference : String
    distributionSystemReference : String
    residualMonitoringReference : String
    disinfectionByproductControlReference : String
    drinkingWaterAuthorityReference : String

open DrinkingWaterChlorineLineage public

------------------------------------------------------------------------
-- Authority boundary.
------------------------------------------------------------------------

record ChlorAlkaliBoundary : Set where
  constructor chlorAlkaliBoundary
  field
    overallStoichiometryIsCompleteCellMechanism : Bool
    overallStoichiometryIsCompleteCellMechanismIsFalse :
      overallStoichiometryIsCompleteCellMechanism ≡ false

    geologicalSaltDirectlyDisinfectsTapWater : Bool
    geologicalSaltDirectlyDisinfectsTapWaterIsFalse :
      geologicalSaltDirectlyDisinfectsTapWater ≡ false

    chlorineProductionReceiptDeterminesSafeWaterDose : Bool
    chlorineProductionReceiptDeterminesSafeWaterDoseIsFalse :
      chlorineProductionReceiptDeterminesSafeWaterDose ≡ false

    allChlorAlkaliCellsHaveSameOperatingEnvelope : Bool
    allChlorAlkaliCellsHaveSameOperatingEnvelopeIsFalse :
      allChlorAlkaliCellsHaveSameOperatingEnvelope ≡ false

    downstreamApplicationRequiresIndependentReceipt : Bool
    downstreamApplicationRequiresIndependentReceiptIsTrue :
      downstreamApplicationRequiresIndependentReceipt ≡ true

canonicalChlorAlkaliBoundary : ChlorAlkaliBoundary
canonicalChlorAlkaliBoundary =
  chlorAlkaliBoundary
    false refl
    false refl
    false refl
    false refl
    true refl
