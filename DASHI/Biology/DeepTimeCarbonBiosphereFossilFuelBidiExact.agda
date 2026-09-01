module DASHI.Biology.DeepTimeCarbonBiosphereFossilFuelBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Biology.PrebioticChemistryLifeInevitabilityBidiExact as Prebiotic
import DASHI.Biology.NaturalSystemsHyperfabricExact as Natural
import DASHI.Core.TrajectoryResidueExact as Residue
import DASHI.Core.ActiveBidiDiscriminatorLoopExact as Bidi

------------------------------------------------------------------------
-- DEEP-TIME CARBON / BIOSPHERE / FOSSIL-FUEL LINEAGE
--
-- Bounded empirical calibration:
-- * USGS coal resources: coal begins as peat accumulated from plant material;
--   burial, chemical/biological reactions, heat and time contribute to
--   coalification.
-- * EIA petroleum formation: crude oil/petroleum is primarily associated with
--   ancient marine/lacustrine organic matter including microorganisms, buried
--   and transformed over geological time by heat and pressure.
--
-- Dinosaurs belong to the evolving biosphere/history but are not installed as
-- the canonical dominant petroleum feedstock.
------------------------------------------------------------------------

data DeepTimeStage : Set where
  prebioticChemistry
  microbialBiosphere
  complexEcosystems
  terrestrialForests
  carboniferousPeatSystems
  mesozoicFaunalWorlds
  organicMatterBurial
  kerogenCoalification
  petroleumGasGeneration
  fossilCarbonReservoir
  industrialExtraction
  industrialCombustion
  atmosphericOceanReturn
  : DeepTimeStage

data OrganicSourceFamily : Set where
  terrestrialPlantMatter
  marineLacustrineMicroorganisms
  mixedSedimentaryOrganicMatter
  vertebrateBiomass
  : OrganicSourceFamily

data FossilCarbonFamily : Set where
  coal petroleum naturalGas : FossilCarbonFamily

record FossilCarbonFormationReceipt : Set where
  constructor fossil-carbon-formation-receipt
  field
    sourceFamily : OrganicSourceFamily
    depositionalEnvironmentReference : String
    burialReference : String
    preservationReference : String
    thermalMaturationReference : String
    pressureDepthReference : String
    geologicalTimeReference : String
    productFamily : FossilCarbonFamily
    provenanceReference : String
    validationReference : String

record DeepTimeCarbonTrajectoryReceipt : Set where
  constructor deep-time-carbon-trajectory-receipt
  field
    prebioticReference : String
    biosphereReference : String
    ecosystemReference : String
    burialReference : String
    fossilisationReference : String
    extractionReference : String
    oxidationCombustionReference : String
    atmosphereOceanReference : String
    trajectoryResidueReference : String
    validationReference : String

prebioticBoundary : Prebiotic.PrebioticChemistryLifeInevitabilityBoundary
prebioticBoundary = Prebiotic.canonicalPrebioticChemistryLifeInevitabilityBoundary

naturalBoundary : Natural.NaturalSystemsBoundary
naturalBoundary = Natural.canonicalNaturalSystemsBoundary

activeBidiBoundary : Bidi.ActiveBidiDiscriminatorLoopBoundary
activeBidiBoundary = Bidi.canonicalActiveBidiDiscriminatorLoopBoundary

record DeepTimeCarbonBiosphereFossilFuelBoundary : Set where
  constructor deep-time-carbon-biosphere-fossil-fuel-boundary
  field
    dinosaursAreCanonicalDominantPetroleumSource : Bool
    dinosaursAreCanonicalDominantPetroleumSourceIsFalse :
      dinosaursAreCanonicalDominantPetroleumSource ≡ false
    carboniferousPlantAccumulationCanContributeToCoalLineage : Bool
    carboniferousPlantAccumulationCanContributeToCoalLineageIsTrue :
      carboniferousPlantAccumulationCanContributeToCoalLineage ≡ true
    marineMicrobialOrganicMatterCanContributeToPetroleumLineage : Bool
    marineMicrobialOrganicMatterCanContributeToPetroleumLineageIsTrue :
      marineMicrobialOrganicMatterCanContributeToPetroleumLineage ≡ true
    fossilCarbonEqualsUnchangedAncientBiomass : Bool
    fossilCarbonEqualsUnchangedAncientBiomassIsFalse :
      fossilCarbonEqualsUnchangedAncientBiomass ≡ false
    presentFuelCompositionRecoversUniqueBiologicalHistory : Bool
    presentFuelCompositionRecoversUniqueBiologicalHistoryIsFalse :
      presentFuelCompositionRecoversUniqueBiologicalHistory ≡ false
    fossilFuelFormationNeedsHistoryBearingTransformationPath : Bool
    fossilFuelFormationNeedsHistoryBearingTransformationPathIsTrue :
      fossilFuelFormationNeedsHistoryBearingTransformationPath ≡ true
    combustionCanReturnGeologicallyStoredCarbonToActiveSurfaceCycle : Bool
    combustionCanReturnGeologicallyStoredCarbonToActiveSurfaceCycleIsTrue :
      combustionCanReturnGeologicallyStoredCarbonToActiveSurfaceCycle ≡ true
    reading : String

canonicalDeepTimeCarbonBiosphereFossilFuelBoundary :
  DeepTimeCarbonBiosphereFossilFuelBoundary
canonicalDeepTimeCarbonBiosphereFossilFuelBoundary =
  deep-time-carbon-biosphere-fossil-fuel-boundary
    false refl
    true refl
    true refl
    false refl
    false refl
    true refl
    true refl
    "Deep-time fossil carbon is a history-bearing transformation product of biological organic matter, depositional environment, burial and maturation. Coal and petroleum have different canonical source/depositional emphases; dinosaurs are part of biospheric history but are not promoted to the dominant petroleum-source story. Industrial combustion reconnects geological carbon reservoirs to active atmosphere-ocean carbon cycling without erasing that provenance."
