module DASHI.Chemistry.DrinkingWaterChlorineSpeciationExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Chemistry.ChlorAlkaliSaltIndustryExact as Industry
import DASHI.Chemistry.TransitionKernel as Chemistry
open Chemistry
import DASHI.Geology.SaltGeochemistryExact as Salt

------------------------------------------------------------------------
-- DRINKING-WATER CHLORINE SPECIATION
--
-- Source anchors:
--   WHO Guidelines for Drinking-water Quality (2026 edition): chlorine in
--   water forms hypochlorous acid/hypochlorite, with relative amounts varying
--   with pH; chlorine residual and treatment performance remain operational
--   monitoring questions rather than consequences of source production alone.
--   US EPA drinking-water/disinfection material: free chlorine chemistry,
--   residual measurement and contact-time performance are distinct surfaces.
--
-- Canonical qualitative chemistry:
--
--   Cl2 + H2O <-> HOCl + H+ + Cl-
--   HOCl <-> H+ + OCl-
--
-- This owner separates source chlorine, aqueous free-chlorine species,
-- measured residual, treatment performance, and regulatory authority.
------------------------------------------------------------------------

hypochlorousAcidSpecies : Chemistry.Species
hypochlorousAcidSpecies = record
  { speciesId = "hypochlorous acid"
  ; phase = Chemistry.dissolved
  ; chargeLabel = "0"
  ; compositionLabel = "HOCl"
  ; mobilityClass = Chemistry.mobile
  ; activityModelLabel = "aqueous acid-base activity model supplied by application"
  ; opticalRoleLabel = "not asserted"
  ; evidence = Chemistry.literatureEstablished
  }

hypochloriteSpecies : Chemistry.Species
hypochloriteSpecies = record
  { speciesId = "hypochlorite ion"
  ; phase = Chemistry.dissolved
  ; chargeLabel = "-1"
  ; compositionLabel = "OCl-"
  ; mobilityClass = Chemistry.mobile
  ; activityModelLabel = "aqueous acid-base activity model supplied by application"
  ; opticalRoleLabel = "not asserted"
  ; evidence = Chemistry.literatureEstablished
  }

protonSpecies : Chemistry.Species
protonSpecies = record
  { speciesId = "aqueous proton bookkeeping species"
  ; phase = Chemistry.dissolved
  ; chargeLabel = "+1"
  ; compositionLabel = "H+"
  ; mobilityClass = Chemistry.mobile
  ; activityModelLabel = "aqueous proton activity model supplied by application"
  ; opticalRoleLabel = "not asserted"
  ; evidence = Chemistry.literatureEstablished
  }

waterTreatmentEnvironment : Chemistry.Environment
waterTreatmentEnvironment = record
  { temperatureCarrier = "water temperature supplied by treatment-state receipt"
  ; pHCarrier = "measured treatment-water pH"
  ; pressureCarrier = "treatment/distribution pressure supplied by application"
  ; humidityCarrier = "not primary state variable"
  ; illuminationCarrier = "photolysis exposure supplied if relevant"
  ; ionicStrengthCarrier = "finished-water ionic-strength/activity model"
  }

chlorineHydrolysisCondition : Chemistry.Condition
chlorineHydrolysisCondition = record
  { conditionLabel = "chlorine hydrolysis in aqueous treatment state"
  ; environment = waterTreatmentEnvironment
  ; guardExpression = "aqueous chlorine present; pH/temperature/activity regime supplied"
  }

hypochlorousDissociationCondition : Chemistry.Condition
hypochlorousDissociationCondition = record
  { conditionLabel = "HOCl/OCl- acid-base speciation"
  ; environment = waterTreatmentEnvironment
  ; guardExpression = "aqueous free chlorine present; pH/temperature/activity regime supplied"
  }

speciationRate : Chemistry.RateLaw
speciationRate = record
  { rateLawKind = Chemistry.massAction
  ; symbolicForm = "equilibrium/speciation law supplied by application"
  ; parameters = []
  ; validityRegime = "aqueous drinking-water chlorine speciation"
  ; evidence = Chemistry.literatureEstablished
  }

chlorineHydrolysisTransition : Chemistry.Transition
chlorineHydrolysisTransition = record
  { transitionId = "chlorine hydrolysis to hypochlorous acid"
  ; transitionKind = Chemistry.chemicalReaction
  ; reactants =
      record { species = Industry.chlorineGasSpecies ; coefficient = 1 }
      ∷ record { species = Industry.waterSpecies ; coefficient = 1 }
      ∷ []
  ; products =
      record { species = hypochlorousAcidSpecies ; coefficient = 1 }
      ∷ record { species = protonSpecies ; coefficient = 1 }
      ∷ record { species = Salt.chlorideIonSpecies ; coefficient = 1 }
      ∷ []
  ; catalysts = []
  ; rateLaw = speciationRate
  ; condition = chlorineHydrolysisCondition
  ; reversibility = Chemistry.reversible
  ; evidence = Chemistry.literatureEstablished
  }

hypochlorousDissociationTransition : Chemistry.Transition
hypochlorousDissociationTransition = record
  { transitionId = "hypochlorous acid dissociation"
  ; transitionKind = Chemistry.chemicalReaction
  ; reactants =
      record { species = hypochlorousAcidSpecies ; coefficient = 1 } ∷ []
  ; products =
      record { species = protonSpecies ; coefficient = 1 }
      ∷ record { species = hypochloriteSpecies ; coefficient = 1 }
      ∷ []
  ; catalysts = []
  ; rateLaw = speciationRate
  ; condition = hypochlorousDissociationCondition
  ; reversibility = Chemistry.reversible
  ; evidence = Chemistry.literatureEstablished
  }

data FreeChlorineSpeciesKind : Set where
  dissolvedMolecularChlorine : FreeChlorineSpeciesKind
  hypochlorousAcid : FreeChlorineSpeciesKind
  hypochloriteIon : FreeChlorineSpeciesKind


record FreeChlorineResidualState : Set₁ where
  constructor freeChlorineResidualState
  field
    treatmentNetwork : Chemistry.ReactionNetwork
    chlorineSource : Chemistry.Species
    sourceIsCanonicalChlorine : chlorineSource ≡ Industry.chlorineGasSpecies
    hydrolysis : Chemistry.Transition
    hydrolysisIsCanonical : hydrolysis ≡ chlorineHydrolysisTransition
    acidBaseSpeciation : Chemistry.Transition
    acidBaseSpeciationIsCanonical : acidBaseSpeciation ≡ hypochlorousDissociationTransition
    pHReference : String
    temperatureReference : String
    freeChlorineMeasurementMethodReference : String
    residualConcentrationReference : String
    contactTimeReference : String
    hydraulicResidenceReference : String
    demandDecayReference : String
    validationReference : String

open FreeChlorineResidualState public

record DrinkingWaterDisinfectionReceipt
    (residual : FreeChlorineResidualState) : Set₁ where
  constructor drinkingWaterDisinfectionReceipt
  field
    organismOrPerformanceTargetReference : String
    doseReference : String
    contactTimeCriterionReference : String
    pHTemperatureCorrectionReference : String
    demandModelReference : String
    treatmentValidationReference : String
    regulatoryAuthorityReference : String
    monitoringFrequencyReference : String

open DrinkingWaterDisinfectionReceipt public

record DrinkingWaterChlorineSpeciationBoundary : Set where
  constructor drinkingWaterChlorineSpeciationBoundary
  field
    chlorineAddedEqualsMeasuredFreeResidual : Bool
    chlorineAddedEqualsMeasuredFreeResidualIsFalse : chlorineAddedEqualsMeasuredFreeResidual ≡ false

    chlorineDoseDeterminesHOClFractionWithoutPH : Bool
    chlorineDoseDeterminesHOClFractionWithoutPHIsFalse : chlorineDoseDeterminesHOClFractionWithoutPH ≡ false

    freeChlorineResidualProvesDisinfectionPerformance : Bool
    freeChlorineResidualProvesDisinfectionPerformanceIsFalse : freeChlorineResidualProvesDisinfectionPerformance ≡ false

    chlorAlkaliProductionDeterminesTreatmentDose : Bool
    chlorAlkaliProductionDeterminesTreatmentDoseIsFalse : chlorAlkaliProductionDeterminesTreatmentDose ≡ false

    chlorideProductOfHydrolysisIdentifiesItsGeologicalSource : Bool
    chlorideProductOfHydrolysisIdentifiesItsGeologicalSourceIsFalse :
      chlorideProductOfHydrolysisIdentifiesItsGeologicalSource ≡ false

    disinfectionNeedsIndependentPerformanceAndRegulatoryReceipts : Bool
    disinfectionNeedsIndependentPerformanceAndRegulatoryReceiptsIsTrue :
      disinfectionNeedsIndependentPerformanceAndRegulatoryReceipts ≡ true

canonicalDrinkingWaterChlorineSpeciationBoundary : DrinkingWaterChlorineSpeciationBoundary
canonicalDrinkingWaterChlorineSpeciationBoundary =
  drinkingWaterChlorineSpeciationBoundary
    false refl false refl false refl false refl false refl true refl
