module DASHI.Chemistry.DrinkingWaterChloramineDBPBoundaryExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Chemistry.ChlorAlkaliSaltIndustryExact as Industry
import DASHI.Chemistry.DrinkingWaterChlorineSpeciationExact as Free
import DASHI.Chemistry.TransitionKernel as Chemistry
open Chemistry

------------------------------------------------------------------------
-- CHLORAMINE / DISINFECTION-BYPRODUCT BOUNDARY
--
-- Source anchors:
--   US EPA, Effectiveness of Disinfectant Residuals in the Distribution
--   System (2007): aqueous chlorine + ammonia competing chloramine chemistry,
--   with pH, chlorine:ammonia ratio, temperature and contact-time dependence.
--   WHO Guidelines for Drinking-water Quality: disinfectants generate distinct
--   organohalogen/inorganic/non-halogenated by-product families and these need
--   separate monitoring/control rather than inference from disinfectant dose.
--
-- Keeps combined chlorine and DBP risk as separate chemistry/monitoring
-- obligations.  It deliberately does not encode one universal breakpoint,
-- dose, CT value, or DBP yield law.
--
-- Canonical qualitative monochloramine bookkeeping:
--
--   NH3 + HOCl -> NH2Cl + H2O
--
-- The broader chloramine family and breakpoint behaviour remain application
-- supplied because pH, chlorine:ammonia ratio, temperature and contact time
-- alter which combined-chlorine species dominate.
------------------------------------------------------------------------

ammoniaSpecies : Chemistry.Species
ammoniaSpecies = record
  { speciesId = "ammonia"
  ; phase = Chemistry.dissolved
  ; chargeLabel = "0 bulk NH3 representation"
  ; compositionLabel = "NH3"
  ; mobilityClass = Chemistry.mobile
  ; activityModelLabel = "aqueous ammonia/ammonium speciation supplied by application"
  ; opticalRoleLabel = "not asserted"
  ; evidence = Chemistry.literatureEstablished
  }

monochloramineSpecies : Chemistry.Species
monochloramineSpecies = record
  { speciesId = "monochloramine"
  ; phase = Chemistry.dissolved
  ; chargeLabel = "0"
  ; compositionLabel = "NH2Cl"
  ; mobilityClass = Chemistry.mobile
  ; activityModelLabel = "aqueous chloramine model supplied by application"
  ; opticalRoleLabel = "not asserted"
  ; evidence = Chemistry.literatureEstablished
  }

chloramineCondition : Chemistry.Condition
chloramineCondition = record
  { conditionLabel = "chloramine formation regime"
  ; environment = Free.waterTreatmentEnvironment
  ; guardExpression = "free chlorine and ammonia/ammonium present; pH, ratio, mixing and time supplied"
  }

chloramineRate : Chemistry.RateLaw
chloramineRate = record
  { rateLawKind = Chemistry.empirical
  ; symbolicForm = "chloramine formation/breakpoint kinetics supplied by treatment model"
  ; parameters = []
  ; validityRegime = "application-specific drinking-water chloramination"
  ; evidence = Chemistry.literatureEstablished
  }

monochloramineFormationTransition : Chemistry.Transition
monochloramineFormationTransition = record
  { transitionId = "monochloramine formation from HOCl and ammonia"
  ; transitionKind = Chemistry.chemicalReaction
  ; reactants =
      record { species = Free.hypochlorousAcidSpecies ; coefficient = 1 }
      ∷ record { species = ammoniaSpecies ; coefficient = 1 }
      ∷ []
  ; products =
      record { species = monochloramineSpecies ; coefficient = 1 }
      ∷ record { species = Industry.waterSpecies ; coefficient = 1 }
      ∷ []
  ; catalysts = []
  ; rateLaw = chloramineRate
  ; condition = chloramineCondition
  ; reversibility = Chemistry.conditionallyReversible
  ; evidence = Chemistry.literatureEstablished
  }

data ResidualKind : Set where
  freeChlorineResidual : ResidualKind
  combinedChlorineResidual : ResidualKind


record CombinedChlorineResidualState : Set₁ where
  constructor combinedChlorineResidualState
  field
    network : Chemistry.ReactionNetwork
    freeChlorineState : Free.FreeChlorineResidualState
    chloramineFormation : Chemistry.Transition
    chloramineFormationIsCanonical : chloramineFormation ≡ monochloramineFormationTransition
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
