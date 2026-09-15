module DASHI.Environment.BiocontrolChemistryObservationFibreExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.AdmissibleConsumerMDLHyperfabricExact as MDL
import DASHI.Environment.BiocontrolChemistry369IndexExact as ChemistryIndex
import DASHI.Environment.BiocontrolSIQuantityExact as SIQuantity

------------------------------------------------------------------------
-- CHEMISTRY-INDEXED OBSERVATION FIBRE
--
-- This owner refines the coarse nutrient-residual surface into the actual
-- chemistry coordinates already demanded by the repository: analyte identity,
-- chemical species/fraction, pH, temperature, hydrology, assay method,
-- provenance and uncertainty.  It does not invent field measurements.
------------------------------------------------------------------------

record ChemistryObservationFibre : Set where
  constructor chemistryObservationFibre
  field
    bulkConcentrationReference : String
    analyteIdentityReference : String
    speciesFractionReference : String
    pHReference : String
    temperatureReference : String
    hydrologyReference : String
    assayMethodReference : String
    uncertaintyReference : String
    sampleTimeWindowReference : String
    siteIdentityReference : String
    provenanceReference : String
    exactNumericObservationPaid : Bool
    chemicalIdentityPaid : Bool

open ChemistryObservationFibre public

canonicalChemistryObservationFibre : ChemistryObservationFibre
canonicalChemistryObservationFibre = chemistryObservationFibre
  "bulk nutrient concentration is only the coarse measurement surface"
  "analyte identity remains a separately paid assay coordinate"
  "nitrate/ammonium/other species and dissolved/total fraction remain separately paid"
  "pH is an independent chemistry/environment coordinate"
  "temperature is an independent kinetics/environment coordinate"
  "flow/residence-time context remains a hydrologic coordinate"
  "assay and sample-preparation method must be source bound"
  "measurement and classification uncertainty must remain explicit"
  "sampling instant/window must be declared"
  "waterbody/site identity must be declared"
  "site/time/sample/method provenance must be retained"
  false
  false

------------------------------------------------------------------------
-- Reuse existing actual-chemistry / 369 / SI boundaries.
------------------------------------------------------------------------

chemistry369Index : ChemistryIndex.BiocontrolChemistry369Index
chemistry369Index = ChemistryIndex.canonicalBiocontrolChemistry369Index

chemistry369Boundary : ChemistryIndex.BiocontrolChemistry369Boundary
chemistry369Boundary = ChemistryIndex.canonicalBiocontrolChemistry369Boundary

siBoundary : SIQuantity.BiocontrolSIQuantityBoundary
siBoundary = SIQuantity.canonicalBiocontrolSIQuantityBoundary

------------------------------------------------------------------------
-- Consumer-indexed observer family.
--
-- The bulk-only observer is admissible as a measurement surface but is not
-- adequate for the declared chemical-species consumer.  The local refinement
-- adds analyte/species/context coordinates without claiming world completeness.
------------------------------------------------------------------------

data ChemistryObserverModel : Set where
  bulkOnly : ChemistryObserverModel
  analyteSpeciesContext : ChemistryObserverModel

data ChemistryRefines : ChemistryObserverModel → ChemistryObserverModel → Set where
  bulkToSpeciated : ChemistryRefines bulkOnly analyteSpeciesContext

ChemistryAdmissible : ChemistryObserverModel → Set
ChemistryAdmissible bulkOnly = ⊤
ChemistryAdmissible analyteSpeciesContext = ⊤

ChemistryConsumerAdequate : ChemistryObserverModel → Set
ChemistryConsumerAdequate bulkOnly = ⊥
ChemistryConsumerAdequate analyteSpeciesContext = ⊤

chemistryDescriptionLength : ChemistryObserverModel → Nat
chemistryDescriptionLength bulkOnly = 1
chemistryDescriptionLength analyteSpeciesContext = 2

chemistryModelReference : ChemistryObserverModel → String
chemistryModelReference bulkOnly =
  "bulk nutrient mass concentration only"
chemistryModelReference analyteSpeciesContext =
  "bulk concentration plus analyte/species/fraction/pH/temperature/hydrology/assay context"

chemistryObservationProblem : MDL.ConsumerMDLProblem
chemistryObservationProblem = MDL.consumerMDLProblem
  ChemistryObserverModel
  ChemistryAdmissible
  ChemistryConsumerAdequate
  chemistryDescriptionLength
  ChemistryRefines
  chemistryModelReference
  "finite repository-local observer complexity rank; not empirical acquisition cost"
  "chemical-species/fraction-sensitive rebound consumer"

bulkOnlyCounterexample :
  MDL.ConsumerCounterexample chemistryObservationProblem bulkOnly
bulkOnlyCounterexample = MDL.consumerCounterexample
  ⊤
  tt
  (λ inadequate → inadequate)
  "bulk concentration erases analyte/speciation/fraction/context distinctions"
  "repo-local counterexample: equal bulk mass class does not determine nitrogen species"

bulkToSpeciatedRepair :
  MDL.LocalRefinementRepair
    chemistryObservationProblem bulkOnly analyteSpeciesContext
bulkToSpeciatedRepair = MDL.localRefinementRepair
  bulkOnlyCounterexample
  bulkToSpeciated
  tt
  tt
  "reopen analyte/species/fraction/pH/temperature/hydrology/assay coordinates while preserving the bulk observation"

repairProvidesSpeciatedEligibility :
  MDL.Eligible chemistryObservationProblem analyteSpeciesContext
repairProvidesSpeciatedEligibility =
  MDL.repairProvidesEligibleRefinement bulkToSpeciatedRepair

------------------------------------------------------------------------
-- Local refinement neighbourhood: repair stays inside the declared aquatic-
-- chemistry observation family rather than switching to an unrelated model.
------------------------------------------------------------------------

data ChemistryObserverAddress : Set where
  aquaticChemistryObserverFamily : ChemistryObserverAddress

chemistryObserverNeighbourhood :
  MDL.RefinementNeighbourhood chemistryObservationProblem
chemistryObserverNeighbourhood = MDL.refinementNeighbourhood
  ChemistryObserverAddress
  (λ model → aquaticChemistryObserverFamily)
  (λ left right → ⊤)
  (λ coarse fine refinement → tt)
  "aquatic chemistry observer family: bulk-only -> analyte/species/context refinement"

repairStaysInChemistryObserverFamily :
  MDL.sameNeighbourhood chemistryObserverNeighbourhood
    (MDL.address chemistryObserverNeighbourhood bulkOnly)
    (MDL.address chemistryObserverNeighbourhood analyteSpeciesContext)
repairStaysInChemistryObserverFamily =
  MDL.repairStaysInDeclaredNeighbourhood
    chemistryObserverNeighbourhood bulkToSpeciatedRepair

------------------------------------------------------------------------
-- Boundary.
------------------------------------------------------------------------

record BiocontrolChemistryObservationBoundary : Set where
  constructor biocontrolChemistryObservationBoundary
  field
    bulkConcentrationIsCompleteChemistry : Bool
    bulkConcentrationIsCompleteChemistryIsFalse :
      bulkConcentrationIsCompleteChemistry ≡ false

    sameBulkConcentrationDeterminesSpeciation : Bool
    sameBulkConcentrationDeterminesSpeciationIsFalse :
      sameBulkConcentrationDeterminesSpeciation ≡ false

    localRepairAddsMissingChemicalCoordinates : Bool
    localRepairAddsMissingChemicalCoordinatesIsTrue :
      localRepairAddsMissingChemicalCoordinates ≡ true

    localRepairInventsFieldMeasurement : Bool
    localRepairInventsFieldMeasurementIsFalse :
      localRepairInventsFieldMeasurement ≡ false

    richerChemistryObserverMeansCompleteMechanism : Bool
    richerChemistryObserverMeansCompleteMechanismIsFalse :
      richerChemistryObserverMeansCompleteMechanism ≡ false

    exactNumericObservationStillRequiresProvenance : Bool
    exactNumericObservationStillRequiresProvenanceIsTrue :
      exactNumericObservationStillRequiresProvenance ≡ true

canonicalBiocontrolChemistryObservationBoundary :
  BiocontrolChemistryObservationBoundary
canonicalBiocontrolChemistryObservationBoundary =
  biocontrolChemistryObservationBoundary
    false refl
    false refl
    true refl
    false refl
    false refl
    true refl
