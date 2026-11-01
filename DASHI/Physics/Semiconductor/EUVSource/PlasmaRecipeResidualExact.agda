{-# OPTIONS --safe #-}

module DASHI.Physics.Semiconductor.EUVSource.PlasmaRecipeResidualExact where

open import Agda.Builtin.Equality using (_≡_; refl)

-- ASML publicly states that higher-power EUV development involved new
-- "plasma recipes" and increased laser/repetition-rate capability, while not
-- publishing a complete current production recipe.  This owner records the
-- resulting evidence shape without guessing the hidden coordinates.

data PublicPlasmaFact : Set where
  DropletFlatteningImprovesOutput : PublicPlasmaFact
  PlasmaRecipeDevelopmentContributed : PublicPlasmaFact
  RepeatRateIncreaseContributed : PublicPlasmaFact
  LaserPowerIncreaseContributed : PublicPlasmaFact

data RecipeCoordinate : Set where
  PrePulseEnergy : RecipeCoordinate
  MainPulseEnergy : RecipeCoordinate
  PulseTemporalShape : RecipeCoordinate
  PulseSpatialProfile : RecipeCoordinate
  InterPulseDelay : RecipeCoordinate
  DropletShapeAtMainPulse : RecipeCoordinate
  LaserDropletAimOffset : RecipeCoordinate
  TinMassPerEvent : RecipeCoordinate
  PlasmaDensityProfile : RecipeCoordinate
  PlasmaElectronTemperatureProfile : RecipeCoordinate
  InBandConversionEfficiency : RecipeCoordinate
  CollectorFacingDebrisDistribution : RecipeCoordinate

-- A coordinate can be known to exist physically while its exact production
-- setting remains unowned by our public-source corpus.
data KnowledgeState : Set where
  PublicQualitative : KnowledgeState
  ExactCurrentValueUnowned : KnowledgeState

record RecipeReceipt : Set where
  constructor recipeReceipt
  field
    coordinate : RecipeCoordinate
    knowledge  : KnowledgeState

open RecipeReceipt public

prePulseEnergyResidual : RecipeReceipt
prePulseEnergyResidual = recipeReceipt PrePulseEnergy ExactCurrentValueUnowned

mainPulseEnergyResidual : RecipeReceipt
mainPulseEnergyResidual = recipeReceipt MainPulseEnergy ExactCurrentValueUnowned

interPulseDelayResidual : RecipeReceipt
interPulseDelayResidual = recipeReceipt InterPulseDelay ExactCurrentValueUnowned

dropletShapeResidual : RecipeReceipt
dropletShapeResidual = recipeReceipt DropletShapeAtMainPulse ExactCurrentValueUnowned

conversionEfficiencyResidual : RecipeReceipt
conversionEfficiencyResidual = recipeReceipt InBandConversionEfficiency ExactCurrentValueUnowned

debrisDistributionResidual : RecipeReceipt
debrisDistributionResidual = recipeReceipt CollectorFacingDebrisDistribution ExactCurrentValueUnowned

-- Firewall: a qualitative public statement that a variable matters is not an
-- exact current operating-point disclosure.
data ⊥ : Set where

qualitativeNotExact : PublicQualitative ≡ ExactCurrentValueUnowned → ⊥
qualitativeNotExact ()
