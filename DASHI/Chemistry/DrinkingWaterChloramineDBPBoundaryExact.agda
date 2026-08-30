module DASHI.Chemistry.DrinkingWaterChloramineDBPBoundaryExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Chemistry.DrinkingWaterChlorineSpeciationExact as Free
import DASHI.Chemistry.TransitionKernel as Chemistry

------------------------------------------------------------------------
-- CHLORAMINE / DISINFECTION-BYPRODUCT BOUNDARY
--
-- Keeps combined chlorine and DBP risk as separate chemistry/monitoring
-- obligations.  It deliberately does not encode one universal breakpoint,
-- dose, CT value, or DBP yield law.
------------------------------------------------------------------------

ammoniaSpecies : Chemistry.Species
ammoniaSpecies = record
  { Chemistry.speciesId = "ammonia"
  ; Chemistry.phase = Chemistry.dissolved
  ; Chemistry.chargeLabel = "0 bulk NH3 representation"
  ; Chemistry.compositionLabel = "NH3"
  ; Chemistry.mobilityClass = Chemistry.mobile
  ; Chemistry.activityModelLabel = "aqueous ammonia/ammonium speciation supplied by application"
  ; Chemistry.opticalRoleLabel = "not asserted"
  ; Chemistry.evidence = Chemistry.literatureEstablished
  }

monochloramineSpecies : Chemistry.Species
monochloramineSpecies = record
  { Chemistry.speciesId = "monochloramine"
  ; Chemistry.phase = Chemistry.dissolved
  ; Chemistry.chargeLabel = "0"
  ; Chemistry.compositionLabel = "NH2Cl"
  ; Chemistry.mobilityClass = Chemistry.mobile
  ; Chemistry.activityModelLabel = "aqueous chloramine model supplied by application"
  ; Chemistry.opticalRoleLabel = "not asserted"
  ; Chemistry.evidence = Chemistry.literatureEstablished
  }

chloramineCondition : Chemistry.Condition
chloramineCondition = record
  { Chemistry.conditionLabel = "chloramine formation regime"
  ; Chemistry.environment = Free.waterTreatmentEnvironment
  ; Chemistry.guardExpression = "free chlorine and ammonia/ammonium present; pH, ratio, mixing and time supplied"
  }

chloramineRate : Chemistry.RateLaw
chloramineRate = record
  { Chemistry.rateLawKind = Chemistry.empirical
  ; Chemistry.symbolicForm = "chloramine formation/breakpoint kinetics supplied by treatment model"
  ; Chemistry.parameters = []
  ; Chemistry.validityRegime = "application-specific drinking-water chloramination"
  ; Chemistry.evidence = Chemistry.literatureEstablished
  }

monochloramineFormationTransition : Chemistry.Transition
monochloramineFormationTransition = record
  { Chemistry.transitionId = "monochloramine formation from HOCl and ammonia"
  ; Chemistry.transitionKind = Chemistry.chemicalReaction
  ; Chemistry.reactants =
      record { Chemistry.species = Free.hypochlorousAcidSpecies ; Chemistry.coefficient = 1 }
      ∷ record { Chemistry.species = ammoniaSpecies ; Chemistry.coefficient = 1 }
      ∷ []
  ; Chemistry.products =
      record { Chemistry.species = monochloramineSpecies ; Chemistry.coefficient = 1 }
      ∷ record { Chemistry.species = Chemistry.Species.species (record { Chemistry.species = Free.protonSpecies ; Chemistry.coefficient = 1 }) ; Chemistry.coefficient = 1 }
      ∷ []
  ; Chemistry.catalysts = []
  ; Chemistry.rateLaw = chloramineRate
  ; Chemistry.condition = chloramineCondition
  ; Chemistry.reversibility = Chemistry.conditionallyReversible
  ; Chemistry.evidence = Chemistry.literatureEstablished
  }

-- The exact water coproduct/proton bookkeeping depends on the chosen acid-base
-- representation, so downstream consumers must use the reference fields below
-- rather than treating this qualitative transition as a complete mass-action
-- plant model.

data ResidualKind : Set where
  freeChlorineResidual
  combinedChlorineResidual
  : ResidualKind

record CombinedChlorineResidualState : Set₁ where
  constructor combinedChlorineResidualState
  field
    network : Chemistry.ReactionNetwork
    freeChlorineState : Free.FreeChlorineResidualState
    chloramineFormation : Chemistry.Transition
    ammoniaSourceReference : String
    ammoniaAmmoniumSpeciationReference : String
    chlorineToAmmoniaRatioReference : String
    breakpointBehaviourReference : String
    combinedResidualMeasurementReference : String
    distributionPersistenceReference : String
    nitrificationControlReference : String
    validationReference : String

open CombinedChlorineResidualState public

record DisinfectionByproductReceipt : Set₁ where
  constructor disinfectionByproductReceipt
  field
    precursorCharacterisationReference : String
    disinfectantExposureReference : String
    pHTemperatureReference : String
    bromideOrOtherHalideReference : String
    formationPotentialReference : String
    targetDBPSpeciesReference : String
    analyticalMethodReference : String
    regulatoryLimitReference : String
    treatmentControlReference : String
    monitoringReference : String
    validationReference : String

open DisinfectionByproductReceipt public

record DrinkingWaterCombinedChlorineBoundary : Set where
  constructor drinkingWaterCombinedChlorineBoundary
  field
    freeResidualEqualsCombinedResidual : Bool
    freeResidualEqualsCombinedResidualIsFalse : freeResidualEqualsCombinedResidual ≡ false

    ammoniaAdditionAutomaticallyCreatesDesiredMonochloramineResidual : Bool
    ammoniaAdditionAutomaticallyCreatesDesiredMonochloramineResidualIsFalse :
      ammoniaAdditionAutomaticallyCreatesDesiredMonochloramineResidual ≡ false

    chloraminePersistenceProvesPrimaryDisinfectionAdequacy : Bool
    chloraminePersistenceProvesPrimaryDisinfectionAdequacyIsFalse :
      chloraminePersistenceProvesPrimaryDisinfectionAdequacy ≡ false

    chlorineExposureWithoutPrecursorsDeterminesDBPYield : Bool
    chlorineExposureWithoutPrecursorsDeterminesDBPYieldIsFalse :
      chlorineExposureWithoutPrecursorsDeterminesDBPYield ≡ false

    lowDBPMeasurementProvesAllDisinfectionByproductsAbsent : Bool
    lowDBPMeasurementProvesAllDisinfectionByproductsAbsentIsFalse :
      lowDBPMeasurementProvesAllDisinfectionByproductsAbsent ≡ false

    combinedChlorineAndDBPNeedIndependentMonitoringReceipts : Bool
    combinedChlorineAndDBPNeedIndependentMonitoringReceiptsIsTrue :
      combinedChlorineAndDBPNeedIndependentMonitoringReceipts ≡ true

canonicalDrinkingWaterCombinedChlorineBoundary : DrinkingWaterCombinedChlorineBoundary
canonicalDrinkingWaterCombinedChlorineBoundary =
  drinkingWaterCombinedChlorineBoundary
    false refl false refl false refl false refl false refl true refl
