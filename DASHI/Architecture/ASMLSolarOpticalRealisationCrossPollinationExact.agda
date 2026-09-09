module DASHI.Architecture.ASMLSolarOpticalRealisationCrossPollinationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Architecture.SemiconductorBuiltEnvironmentCrossPollinationExact as Semiconductor
import DASHI.Physics.Foundations.PathIntegralExperimentalSourceRegistryExact as Sources

------------------------------------------------------------------------
-- ASML / SOLAR / OPTICAL REALISATION CROSS-POLLINATION
--
-- Source attribution is deliberately bounded:
-- * ASML is authority for lithography as precision optical projection and for
--   computational lithography as calibrated process modelling.
-- * ASML material mentions chips used in solar-panel monitoring applications.
-- * This does NOT attribute photovoltaic-cell manufacture to ASML.
--
-- The reusable architecture is:
--   intended pattern / function
--     -> calibrated optical/process model
--     -> realised geometry
--     -> fabricated device
--     -> measured outcome.
------------------------------------------------------------------------

asmlLithographyPrinciples : Sources.SourceReference
asmlLithographyPrinciples = Sources.sourceReference
  "ASML"
  "Lithography principles"
  "ASML Technology"
  2026
  "https://www.asml.com/en/technology/lithography-principles"
  "official source for lithography as optical projection of a mask pattern through precision optics onto a photosensitive wafer; not authority that representation correctness guarantees fabricated-device performance"

asmlComputationalLithography : Sources.SourceReference
asmlComputationalLithography = Sources.sourceReference
  "ASML"
  "Computational lithography"
  "ASML Products"
  2026
  "https://www.asml.com/en/products/computational-lithography"
  "official source for calibrated algorithmic models of lithographic manufacturing used to compensate optical/process deformation; supports model-calibration and measured-wafer feedback roles only"

asmlSolarApplicationMention : Sources.SourceReference
asmlSolarApplicationMention = Sources.sourceReference
  "ASML"
  "The popularity of maturity"
  "ASML Stories"
  2023
  "https://www.asml.com/en/company/stories/2023/the-popularity-of-maturity"
  "official ASML example that chips made using mature lithography can appear in systems associated with solar-panel energy monitoring; does not say ASML fabricates photovoltaic panels or cells"

data RealisationLayer : Set where
  intendedPattern : RealisationLayer
  calibratedModel : RealisationLayer
  maskOrOpticalPattern : RealisationLayer
  fabricatedSemiconductor : RealisationLayer
  photovoltaicSystem : RealisationLayer
  siteDeployedEnergySystem : RealisationLayer

record CalibratedManufacturingRealisation : Set₁ where
  constructor calibrated-manufacturing-realisation
  field
    source : Sources.SourceReference
    designIntent : String
    calibratedProcessModel : String
    modelCalibrationDataset : String
    realisedPattern : String
    fabricationReceipt : String
    metrologyReceipt : String
    measuredOutcome : String

open CalibratedManufacturingRealisation public

record SemiconductorToSolarApplicationBridge : Set₁ where
  constructor semiconductor-to-solar-application-bridge
  field
    semiconductorRealisation : Semiconductor.DesignExecutionSystem
    chipApplicationEvidence : Sources.SourceReference
    photovoltaicOrSolarSystemRole : String
    siteDeploymentEvidence : String

open SemiconductorToSolarApplicationBridge public

------------------------------------------------------------------------
-- Non-promotion boundaries.
------------------------------------------------------------------------

data ASMLManufacturesSolarPanels : Set where
asmlSourceDoesNotEstablishSolarPanelManufacture : ASMLManufacturesSolarPanels → ⊥
asmlSourceDoesNotEstablishSolarPanelManufacture ()

data ComputationalLithographyModelGuaranteesFabrication : Set where
computationalLithographyDoesNotGuaranteeFabrication :
  ComputationalLithographyModelGuaranteesFabrication → ⊥
computationalLithographyDoesNotGuaranteeFabrication ()

data FabricatedChipImpliesSuitableSolarDeployment : Set where
fabricatedChipDoesNotImplySuitableSolarDeployment :
  FabricatedChipImpliesSuitableSolarDeployment → ⊥
fabricatedChipDoesNotImplySuitableSolarDeployment ()
