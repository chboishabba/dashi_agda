module DASHI.Chemistry.ChlorAlkaliSaltIndustryExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Chemistry.TransitionKernel as Chemistry
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
  { Chemistry.speciesId = "water"
  ; Chemistry.phase = Chemistry.liquid
  ; Chemistry.chargeLabel = "0"
  ; Chemistry.compositionLabel = "H2O"
  ; Chemistry.mobilityClass = Chemistry.mobile
  ; Chemistry.activityModelLabel = "aqueous solvent model supplied by application"
  ; Chemistry.opticalRoleLabel = "not asserted"
  ; Chemistry.evidence = Chemistry.literatureEstablished
  }

chlorineGasSpecies : Chemistry.Species
chlorineGasSpecies = record
  { Chemistry.speciesId = "chlorine gas"
  ; Chemistry.phase = Chemistry.gas
  ; Chemistry.chargeLabel = "0"
  ; Chemistry.compositionLabel = "Cl2"
  ; Chemistry.mobilityClass = Chemistry.volatile
  ; Chemistry.activityModelLabel = "gas activity/fugacity model supplied by application"
  ; Chemistry.opticalRoleLabel = "not asserted"
  ; Chemistry.evidence = Chemistry.literatureEstablished
  }

hydrogenGasSpecies : Chemistry.Species
hydrogenGasSpecies = record
  { Chemistry.speciesId = "hydrogen gas"
  ; Chemistry.phase = Chemistry.gas
  ; Chemistry.chargeLabel = "0"
  ; Chemistry.compositionLabel = "H2"
  ; Chemistry.mobilityClass = Chemistry.volatile
  ; Chemistry.activityModelLabel = "gas activity/fugacity model supplied by application"
  ; Chemistry.opticalRoleLabel = "not asserted"
  ; Chemistry.evidence = Chemistry.literatureEstablished
  }

sodiumHydroxideSpecies : Chemistry.Species
sodiumHydroxideSpecies = record
  { Chemistry.speciesId = "sodium hydroxide in product liquor"
  ; Chemistry.phase = Chemistry.dissolved
  ; Chemistry.chargeLabel = "bulk neutral electrolyte/product representation"
  ; Chemistry.compositionLabel = "NaOH"
  ; Chemistry.mobilityClass = Chemistry.mobile
  ; Chemistry.activityModelLabel = "strong-electrolyte product model supplied by application"
  ; Chemistry.opticalRoleLabel = "not asserted"
  ; Chemistry.evidence = Chemistry.literatureEstablished
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
  { Chemistry.rateLawKind = Chemistry.empirical
  ; Chemistry.symbolicForm = "electrolysis-controlled chlor-alkali rate supplied by plant model"
  ; Chemistry.parameters = []
  ; Chemistry.validityRegime = "purified brine and cell-specific electrochemical regime"
  ; Chemistry.evidence = Chemistry.literatureEstablished
  }

chlorAlkaliEnvironment : Chemistry.Environment
chlorAlkaliEnvironment = record
  { Chemistry.temperatureCarrier = "cell operating temperature supplied by plant receipt"
  ; Chemistry.pHCarrier = "anolyte/catholyte pH supplied by cell model"
  ; Chemistry.pressureCarrier = "cell/product pressure supplied by plant receipt"
  ; Chemistry.humidityCarrier = "not primary state variable"
  ; Chemistry.illuminationCarrier = "not primary state variable"
  ; Chemistry.ionicStrengthCarrier = "purified concentrated brine ionic-strength model"
  }

chlorAlkaliCondition : Chemistry.Condition
chlorAlkaliCondition = record
  { Chemistry.conditionLabel = "electrolytic chlor-alkali operation"
  ; Chemistry.environment = chlorAlkaliEnvironment
  ; Chemistry.guardExpression = "cell energised; brine purification and separator obligations satisfied"
  }

chlorAlkaliOverallTransition : Chemistry.Transition
chlorAlkaliOverallTransition = record
  { Chemistry.transitionId = "overall chlor-alkali electrolysis"
  ; Chemistry.transitionKind = Chemistry.chemicalReaction
  ; Chemistry.reactants =
      record { Chemistry.species = Salt.haliteSpecies ; Chemistry.coefficient = 2 }
      ∷ record { Chemistry.species = waterSpecies ; Chemistry.coefficient = 2 }
      ∷ []
  ; Chemistry.products =
      record { Chemistry.species = chlorineGasSpecies ; Chemistry.coefficient = 1 }
      ∷ record { Chemistry.species = hydrogenGasSpecies ; Chemistry.coefficient = 1 }
      ∷ record { Chemistry.species = sodiumHydroxideSpecies ; Chemistry.coefficient = 2 }
      ∷ []
  ; Chemistry.catalysts = []
  ; Chemistry.rateLaw = chlorAlkaliRate
  ; Chemistry.condition = chlorAlkaliCondition
  ; Chemistry.reversibility = Chemistry.irreversible
  ; Chemistry.evidence = Chemistry.literatureEstablished
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
  drinkingWaterPrimaryDisinfection
  drinkingWaterSecondaryDisinfectantProduction
  sodiumHypochloriteProduction
  hydrochloricAcidProduction
  vinylChloridePVCChain
  pulpPaperBleachingChemistry
  industrialOxidationChlorination
  : ChlorineApplicationKind

data CausticApplicationKind : Set where
  waterTreatmentPHControl
  pulpPaperCausticProcessing
  soapDetergentChemistry
  aluminaProcessing
  generalIndustrialNeutralisation
  : CausticApplicationKind

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
