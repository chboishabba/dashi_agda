module DASHI.Chemistry.AlliumMolecularTrajectoryExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- ALLIUM MOLECULAR TRAJECTORY
--
-- Source anchors:
--   Borlinghaus et al. 2021, Molecules 26:1505, PMID 33801955.
--   Garlic organosulfur chemistry reviews describing allicin conversion into
--   polysulfanes, vinyl dithiins and ajoene under processing/thermal contexts.
--
-- Purpose: represent the preparation as a time- and context-indexed chemical
-- state rather than a static ingredient list.  This is a qualitative identity
-- and provenance layer; it does not install measured eyesalve concentrations
-- or a complete kinetic model.
------------------------------------------------------------------------

data AlliumSpecies : Set where
  alliin
  allylSulfenicAcid
  allicin
  diallylDisulfide
  diallylTrisulfide
  diallylTetrasulfide
  vinylDithiin
  eAjoene
  zAjoene
  allylMercaptan
  sAllylCysteine
  : AlliumSpecies

record SpeciesIdentity : Set where
  constructor speciesIdentity
  field
    species : AlliumSpecies
    formula : String
    structuralReference : String
    sourceReference : String

open SpeciesIdentity public

allicinIdentity : SpeciesIdentity
allicinIdentity = speciesIdentity allicin "C6H10OS2"
  "diallyl thiosulfinate; PubChem CID 65036"
  "PubChem; Borlinghaus et al. 2021 PMID 33801955"

dadsIdentity : SpeciesIdentity
dadsIdentity = speciesIdentity diallylDisulfide "C6H10S2"
  "diallyl disulfide"
  "garlic organosulfur chemistry literature"

datsIdentity : SpeciesIdentity
datsIdentity = speciesIdentity diallylTrisulfide "C6H10S3"
  "diallyl trisulfide"
  "garlic organosulfur chemistry literature"

ajoeneIdentity : SpeciesIdentity
ajoeneIdentity = speciesIdentity eAjoene "C9H14OS3"
  "(E)-ajoene"
  "PubChem and garlic organosulfur chemistry literature"

data TransformationDriver : Set where
  tissueDisruption
  alliinasePLP
  spontaneousCondensation
  time
  temperature
  solvent
  pH
  metalContact
  biologicalThiol
  redoxEnvironment
  : TransformationDriver

record TransformationReceipt : Set where
  constructor transformationReceipt
  field
    input : AlliumSpecies
    output : AlliumSpecies
    driver : TransformationDriver
    sourceReference : String
    targetPreparationMeasured : Bool
    interpretation : String

open TransformationReceipt public

alliinToSulfenic : TransformationReceipt
alliinToSulfenic = transformationReceipt alliin allylSulfenicAcid alliinasePLP
  "alliinase pathway literature"
  false
  "source-backed Allium pathway; exact target-preparation rate remains unmeasured"

sulfenicToAllicin : TransformationReceipt
sulfenicToAllicin = transformationReceipt allylSulfenicAcid allicin spontaneousCondensation
  "alliin/allicin pathway literature"
  false
  "two allyl-sulfenic-acid molecules condense to allicin; kinetic details remain context-indexed"

allicinToDADS : TransformationReceipt
allicinToDADS = transformationReceipt allicin diallylDisulfide time
  "Borlinghaus et al. 2021 PMID 33801955; related garlic-processing literature"
  false
  "known downstream organosulfur chemistry; not yet measured across Bald's eyesalve maturation"

allicinToDATS : TransformationReceipt
allicinToDATS = transformationReceipt allicin diallylTrisulfide time
  "Borlinghaus et al. 2021 PMID 33801955; related garlic-processing literature"
  false
  "candidate downstream trajectory under preparation-dependent chemistry"

allicinToAjoene : TransformationReceipt
allicinToAjoene = transformationReceipt allicin eAjoene solvent
  "garlic organosulfur processing literature"
  false
  "ajoene formation is context-dependent and must not be assumed present without direct target-preparation chemistry"

record PreparationChemicalState : Set where
  constructor preparationChemicalState
  field
    dayIndex : Nat
    temperatureReference : String
    pHReference : String
    solventReference : String
    metalContactReference : String
    sulfurSpeciationReference : String
    quantitativeProfileReference : String

open PreparationChemicalState public

record PreparationTrajectoryWeld : Set where
  constructor preparationTrajectoryWeld
  field
    freshState : PreparationChemicalState
    maturedState : PreparationChemicalState
    preparationProtocolReference : String
    metabolomicTimeCourseReference : String
    compoundSpecificTimeCourseReference : String
    phenotypeTimeCourseReference : String
    chemistryPhenotypeMediationReference : String

open PreparationTrajectoryWeld public

record MolecularTrajectoryBoundary : Set where
  constructor molecularTrajectoryBoundary
  field
    ingredientListDeterminesMaturedComposition : Bool
    ingredientListDeterminesMaturedCompositionIsFalse :
      ingredientListDeterminesMaturedComposition ≡ false

    knownGarlicTransformationProvesEyesalveTransformation : Bool
    knownGarlicTransformationProvesEyesalveTransformationIsFalse :
      knownGarlicTransformationProvesEyesalveTransformation ≡ false

    sameStartingIngredientsForceSameChemicalTrajectory : Bool
    sameStartingIngredientsForceSameChemicalTrajectoryIsFalse :
      sameStartingIngredientsForceSameChemicalTrajectory ≡ false

    nineDayInstructionShouldBeModelledAsChemicalHistory : Bool
    nineDayInstructionShouldBeModelledAsChemicalHistoryIsTrue :
      nineDayInstructionShouldBeModelledAsChemicalHistory ≡ true

    directTimeResolvedChemicalProfilingWouldRefineMechanism : Bool
    directTimeResolvedChemicalProfilingWouldRefineMechanismIsTrue :
      directTimeResolvedChemicalProfilingWouldRefineMechanism ≡ true

canonicalMolecularTrajectoryBoundary : MolecularTrajectoryBoundary
canonicalMolecularTrajectoryBoundary = molecularTrajectoryBoundary
  false refl false refl false refl true refl true refl
