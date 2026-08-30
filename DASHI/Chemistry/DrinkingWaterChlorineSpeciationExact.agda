module DASHI.Chemistry.DrinkingWaterChlorineSpeciationExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Chemistry.ChlorAlkaliSaltIndustryExact as Industry
import DASHI.Chemistry.TransitionKernel as Chemistry
import DASHI.Geology.SaltGeochemistryExact as Salt

------------------------------------------------------------------------
-- DRINKING-WATER CHLORINE SPECIATION
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
  { Chemistry.speciesId = "hypochlorous acid"
  ; Chemistry.phase = Chemistry.dissolved
  ; Chemistry.chargeLabel = "0"
  ; Chemistry.compositionLabel = "HOCl"
  ; Chemistry.mobilityClass = Chemistry.mobile
  ; Chemistry.activityModelLabel = "aqueous acid-base activity model supplied by application"
  ; Chemistry.opticalRoleLabel = "not asserted"
  ; Chemistry.evidence = Chemistry.literatureEstablished
  }

hypochloriteSpecies : Chemistry.Species
hypochloriteSpecies = record
  { Chemistry.speciesId = "hypochlorite ion"
  ; Chemistry.phase = Chemistry.dissolved
  ; Chemistry.chargeLabel = "-1"
  ; Chemistry.compositionLabel = "OCl-"
  ; Chemistry.mobilityClass = Chemistry.mobile
  ; Chemistry.activityModelLabel = "aqueous acid-base activity model supplied by application"
  ; Chemistry.opticalRoleLabel = "not asserted"
  ; Chemistry.evidence = Chemistry.literatureEstablished
  }

protonSpecies : Chemistry.Species
protonSpecies = record
  { Chemistry.speciesId = "aqueous proton bookkeeping species"
  ; Chemistry.phase = Chemistry.dissolved
  ; Chemistry.chargeLabel = "+1"
  ; Chemistry.compositionLabel = "H+"
  ; Chemistry.mobilityClass = Chemistry.mobile
  ; Chemistry.activityModelLabel = "aqueous proton activity model supplied by application"
  ; Chemistry.opticalRoleLabel = "not asserted"
  ; Chemistry.evidence = Chemistry.literatureEstablished
  }

waterTreatmentEnvironment : Chemistry.Environment
waterTreatmentEnvironment = record
  { Chemistry.temperatureCarrier = "water temperature supplied by treatment-state receipt"
  ; Chemistry.pHCarrier = "measured treatment-water pH"
  ; Chemistry.pressureCarrier = "treatment/distribution pressure supplied by application"
  ; Chemistry.humidityCarrier = "not primary state variable"
  ; Chemistry.illuminationCarrier = "photolysis exposure supplied if relevant"
  ; Chemistry.ionicStrengthCarrier = "finished-water ionic-strength/activity model"
  }

chlorineHydrolysisCondition : Chemistry.Condition
chlorineHydrolysisCondition = record
  { Chemistry.conditionLabel = "chlorine hydrolysis in aqueous treatment state"
  ; Chemistry.environment = waterTreatmentEnvironment
  ; Chemistry.guardExpression = "aqueous chlorine present; pH/temperature/activity regime supplied"
  }

hypochlorousDissociationCondition : Chemistry.Condition
hypochlorousDissociationCondition = record
  { Chemistry.conditionLabel = "HOCl/OCl- acid-base speciation"
  ; Chemistry.environment = waterTreatmentEnvironment
  ; Chemistry.guardExpression = "aqueous free chlorine present; pH/temperature/activity regime supplied"
  }

speciationRate : Chemistry.RateLaw
speciationRate = record
  { Chemistry.rateLawKind = Chemistry.massAction
  ; Chemistry.symbolicForm = "equilibrium/speciation law supplied by application"
  ; Chemistry.parameters = []
  ; Chemistry.validityRegime = "aqueous drinking-water chlorine speciation"
  ; Chemistry.evidence = Chemistry.literatureEstablished
  }

chlorineHydrolysisTransition : Chemistry.Transition
chlorineHydrolysisTransition = record
  { Chemistry.transitionId = "chlorine hydrolysis to hypochlorous acid"
  ; Chemistry.transitionKind = Chemistry.chemicalReaction
  ; Chemistry.reactants =
      record { Chemistry.species = Industry.chlorineGasSpecies ; Chemistry.coefficient = 1 }
      ∷ record { Chemistry.species = Industry.waterSpecies ; Chemistry.coefficient = 1 }
      ∷ []
  ; Chemistry.products =
      record { Chemistry.species = hypochlorousAcidSpecies ; Chemistry.coefficient = 1 }
      ∷ record { Chemistry.species = protonSpecies ; Chemistry.coefficient = 1 }
      ∷ record { Chemistry.species = Salt.chlorideIonSpecies ; Chemistry.coefficient = 1 }
      ∷ []
  ; Chemistry.catalysts = []
  ; Chemistry.rateLaw = speciationRate
  ; Chemistry.condition = chlorineHydrolysisCondition
  ; Chemistry.reversibility = Chemistry.reversible
  ; Chemistry.evidence = Chemistry.literatureEstablished
  }

hypochlorousDissociationTransition : Chemistry.Transition
hypochlorousDissociationTransition = record
  { Chemistry.transitionId = "hypochlorous acid dissociation"
  ; Chemistry.transitionKind = Chemistry.chemicalReaction
  ; Chemistry.reactants =
      record { Chemistry.species = hypochlorousAcidSpecies ; Chemistry.coefficient = 1 } ∷ []
  ; Chemistry.products =
      record { Chemistry.species = protonSpecies ; Chemistry.coefficient = 1 }
      ∷ record { Chemistry.species = hypochloriteSpecies ; Chemistry.coefficient = 1 }
      ∷ []
  ; Chemistry.catalysts = []
  ; Chemistry.rateLaw = speciationRate
  ; Chemistry.condition = hypochlorousDissociationCondition
  ; Chemistry.reversibility = Chemistry.reversible
  ; Chemistry.evidence = Chemistry.literatureEstablished
  }

data FreeChlorineSpeciesKind : Set where
  dissolvedMolecularChlorine
  hypochlorousAcid
  hypochloriteIon
  : FreeChlorineSpeciesKind

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
