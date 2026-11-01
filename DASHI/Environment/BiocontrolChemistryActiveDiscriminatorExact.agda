module DASHI.Environment.BiocontrolChemistryActiveDiscriminatorExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.ConsumerIndexedResidualRefinementExact as Consumer
import DASHI.Core.DiscriminatorSynthesisExact as Synthesis
import DASHI.Core.SequentialConsumerExperimentPlannerExact as Planner
import DASHI.Environment.BiocontrolChemistry369IndexExact as ChemistryIndex
import DASHI.Environment.BiocontrolChemistryObservationFibreExact as ChemistryFibre
import DASHI.Environment.BiocontrolCalibratedEcologicalClassificationExact as Calibration

------------------------------------------------------------------------
-- CHEMISTRY-INDEXED ACTIVE DISCRIMINATOR
--
-- Reuse the generic proof-search experiment spine on the actual chemistry
-- collision: equal bulk nutrient mass surface, different nitrogen-species
-- consumer.  The selected discriminator observes the erased species axis.
------------------------------------------------------------------------

bulkNutrientSpeciesCollision :
  Consumer.ConsumerRelevantCollision
    ChemistryIndex.bulkNutrientObserver ChemistryIndex.nitrogenSpeciesConsumer
bulkNutrientSpeciesCollision = Consumer.consumer-relevant-collision
  ChemistryIndex.nitrateWorld
  ChemistryIndex.ammoniumWorld
  refl
  (λ ())

speciesExperimentBundle :
  Synthesis.ExperimentBundle ChemistryIndex.AquaticChemistryWorld
speciesExperimentBundle = Synthesis.experimentBundle
  ChemistryIndex.NitrogenSpeciesState
  ChemistryIndex.nitrogenSpeciesConsumer
  1
  "nitrogen-species discriminator selected by equal-bulk-mass collision"
  "analyte/species/fraction assay with source-bound protocol and provenance"

pHExperimentBundle :
  Synthesis.ExperimentBundle ChemistryIndex.AquaticChemistryWorld
pHExperimentBundle = Synthesis.experimentBundle
  ChemistryIndex.PHContext
  ChemistryIndex.pHContext
  1
  "pH context probe retained as an independent chemistry coordinate"
  "source-bound pH measurement; not a substitute for species identification"

speciesBundleSeparatesCollision :
  Synthesis.BundleSeparates
    speciesExperimentBundle
    ChemistryIndex.nitrateWorld
    ChemistryIndex.ammoniumWorld
speciesBundleSeparatesCollision = Synthesis.bundleSeparates (λ ())

allChemistryHypothesesLive : ChemistryIndex.AquaticChemistryWorld → Set
allChemistryHypothesesLive world = ⊤

nitrateObservedFibre : ChemistryIndex.AquaticChemistryWorld → Set
nitrateObservedFibre = Planner.RefineByBundle
  allChemistryHypothesesLive
  speciesExperimentBundle
  ChemistryIndex.nitrateDominant

nitrateWorldRemainsLive : nitrateObservedFibre ChemistryIndex.nitrateWorld
nitrateWorldRemainsLive = tt , refl

------------------------------------------------------------------------
-- Cross-pollinated repair/calibration receipts.
------------------------------------------------------------------------

chemistryObserverRepair :
  ChemistryFibre.BiocontrolChemistryObservationBoundary
chemistryObserverRepair =
  ChemistryFibre.canonicalBiocontrolChemistryObservationBoundary

classificationBoundary : Calibration.BiocontrolCalibrationBoundary
classificationBoundary = Calibration.canonicalBiocontrolCalibrationBoundary

record BiocontrolChemistryActiveDiscriminatorReceipt : Set₁ where
  constructor biocontrolChemistryActiveDiscriminatorReceipt
  field
    collision : Consumer.ConsumerRelevantCollision
      ChemistryIndex.bulkNutrientObserver ChemistryIndex.nitrogenSpeciesConsumer
    discriminator : Synthesis.BundleSeparates
      speciesExperimentBundle ChemistryIndex.nitrateWorld ChemistryIndex.ammoniumWorld
    realisedRefinement : nitrateObservedFibre ChemistryIndex.nitrateWorld
    observationFibreBoundary : ChemistryFibre.BiocontrolChemistryObservationBoundary
    calibrationBoundary : Calibration.BiocontrolCalibrationBoundary
    searchReference : String

canonicalBiocontrolChemistryActiveDiscriminator :
  BiocontrolChemistryActiveDiscriminatorReceipt
canonicalBiocontrolChemistryActiveDiscriminator =
  biocontrolChemistryActiveDiscriminatorReceipt
    bulkNutrientSpeciesCollision
    speciesBundleSeparatesCollision
    nitrateWorldRemainsLive
    ChemistryFibre.canonicalBiocontrolChemistryObservationBoundary
    Calibration.canonicalBiocontrolCalibrationBoundary
    "equal bulk nutrient surface -> species-sensitive collision -> source-bound species assay -> refined live chemistry fibre -> contextual ecological classification remains a separate downstream gate"

record BiocontrolChemistryActiveDiscriminatorBoundary : Set where
  constructor biocontrolChemistryActiveDiscriminatorBoundary
  field
    measureAllChemistryCoordinatesByDefault : Bool
    measureAllChemistryCoordinatesByDefaultIsFalse :
      measureAllChemistryCoordinatesByDefault ≡ false

    selectedSpeciesProbeSeparatesDeclaredCollision : Bool
    selectedSpeciesProbeSeparatesDeclaredCollisionIsTrue :
      selectedSpeciesProbeSeparatesDeclaredCollision ≡ true

    pHAloneReplacesSpeciesIdentity : Bool
    pHAloneReplacesSpeciesIdentityIsFalse :
      pHAloneReplacesSpeciesIdentity ≡ false

    speciesObservationAutomaticallyClassifiesEcologicalOutcome : Bool
    speciesObservationAutomaticallyClassifiesEcologicalOutcomeIsFalse :
      speciesObservationAutomaticallyClassifiesEcologicalOutcome ≡ false

    activeSearchInventsFieldMeasurement : Bool
    activeSearchInventsFieldMeasurementIsFalse :
      activeSearchInventsFieldMeasurement ≡ false

canonicalBiocontrolChemistryActiveDiscriminatorBoundary :
  BiocontrolChemistryActiveDiscriminatorBoundary
canonicalBiocontrolChemistryActiveDiscriminatorBoundary =
  biocontrolChemistryActiveDiscriminatorBoundary
    false refl
    true refl
    false refl
    false refl
    false refl
