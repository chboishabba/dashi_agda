module DASHI.Environment.KoreanNaturalFarmingExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; []; _∷_)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- KOREAN NATURAL FARMING (KNF): SOURCE-BOUND PRACTICE SURFACE
--
-- Source lineage:
--   Han Kyu Cho / Atsushi Koyama, Korean Natural Farming (1997)
--   University of Hawai'i CTAHR extension/research materials on KNF / IMO.
--
-- Formal boundary:
-- This is a typed representation of a practice family and its evidence needs.
-- It does not assert universal yield, disease-control, soil-health, or
-- sustainability effects.  Practice identity, proposed mechanism and measured
-- outcome remain different coordinates.
------------------------------------------------------------------------

data KNFPreparationKind : Set where
  indigenousMicroorganismCulture
  fermentedPlantInput
  fermentedAnimalInput
  mineralInput
  herbalInput
  mixedCompostInput : KNFPreparationKind

data MaterialOrigin : Set where
  localFarm localLandscape externallyPurchased : MaterialOrigin

data PreparationProcess : Set where
  collectCulture ferment preserve propagate dilute compost : PreparationProcess

data ApplicationTarget : Set where
  soil rootZone foliage compostPile livestockEnvironment : ApplicationTarget

data EvidenceStatus : Set where
  traditionalPractice extensionGuidance controlledTrial fieldObservation replicatedStudy : EvidenceStatus

data OutcomeCoordinate : Set where
  soilMicrobialCommunity nutrientAvailability cropYield plantHealth pestPressure inputDependence cost : OutcomeCoordinate

record KNFPreparation : Set where
  constructor knf-preparation
  field
    kind : KNFPreparationKind
    origin : MaterialOrigin
    process : List PreparationProcess
    preparationProvenance : String

open KNFPreparation public

record KNFApplication : Set where
  constructor knf-application
  field
    preparation : KNFPreparation
    target : ApplicationTarget
    dilutionOrDose : String
    timingContext : String
    siteContext : String

open KNFApplication public

record KNFOutcomeEvidence : Set where
  constructor knf-outcome-evidence
  field
    application : KNFApplication
    outcome : OutcomeCoordinate
    evidenceStatus : EvidenceStatus
    resultSummary : String
    sourceCitation : String

open KNFOutcomeEvidence public

------------------------------------------------------------------------
-- Indigenous microorganism pathway.
--
-- The KNF identity is not "microbes are always beneficial".  It is a local
-- collection / propagation practice whose agronomic consequence must still be
-- established by application-specific evidence.
------------------------------------------------------------------------

canonicalIMO : KNFPreparation
canonicalIMO =
  knf-preparation
    indigenousMicroorganismCulture
    localLandscape
    (collectCulture ∷ preserve ∷ propagate ∷ [])
    "Cho & Koyama 1997; University of Hawai'i CTAHR KNF/IMO extension materials"

record LocalMicrobialInoculationContract : Set where
  constructor local-microbial-inoculation-contract
  field
    inoculum : KNFPreparation
    localOrigin : origin inoculum ≡ localLandscape
    soilApplication : KNFApplication
    samePreparation : preparation soilApplication ≡ inoculum
    outcomeEvidence : List KNFOutcomeEvidence

open LocalMicrobialInoculationContract public

------------------------------------------------------------------------
-- Local-input / permaculture-compatible accounting surface.
--
-- A preparation made from local biological residues may reduce some imported
-- material flows while simultaneously requiring labour, carbohydrate feed,
-- containers, water, time and other inputs.  Therefore "local" is not
-- definitionally "free", "zero energy", or "zero external input".
------------------------------------------------------------------------

record KNFResourceFootprint : Set where
  constructor knf-resource-footprint
  field
    preparation : KNFPreparation
    localBiologicalMaterial : Bool
    importedMaterialRequired : Bool
    labourRequired : Bool
    waterRequired : Bool
    fermentationTimeRequired : Bool
    embodiedEnergyAccountingRequired : Bool

open KNFResourceFootprint public

canonicalIMOResourceFootprint : KNFResourceFootprint
canonicalIMOResourceFootprint =
  knf-resource-footprint
    canonicalIMO
    true
    false
    true
    true
    true
    true

------------------------------------------------------------------------
-- Evidence gates.
------------------------------------------------------------------------

data PracticeMeansMechanismPermission : Set where

data MechanismMeansOutcomePermission : Set where

data LocalMeansBeneficialPermission : Set where

data KNFMeansZeroExternalInputPermission : Set where

data OneTrialMeansUniversalAgronomicEffectPermission : Set where

data NaturalMeansSafePermission : Set where

practiceDoesNotProveMechanism : PracticeMeansMechanismPermission → ⊥
practiceDoesNotProveMechanism ()

mechanismDoesNotProveOutcome : MechanismMeansOutcomePermission → ⊥
mechanismDoesNotProveOutcome ()

localDoesNotAutomaticallyMeanBeneficial : LocalMeansBeneficialPermission → ⊥
localDoesNotAutomaticallyMeanBeneficial ()

knfDoesNotDefinitionallyMeanZeroExternalInput : KNFMeansZeroExternalInputPermission → ⊥
knfDoesNotDefinitionallyMeanZeroExternalInput ()

oneTrialDoesNotEstablishUniversalEffect : OneTrialMeansUniversalAgronomicEffectPermission → ⊥
oneTrialDoesNotEstablishUniversalEffect ()

naturalDoesNotByItselfEstablishSafety : NaturalMeansSafePermission → ⊥
naturalDoesNotByItselfEstablishSafety ()

record KoreanNaturalFarmingBoundary : Set where
  constructor korean-natural-farming-boundary
  field
    knfIsRepresentedAsPracticeFamily : Bool
    indigenousMicroorganismsAreFirstClassPreparation : Bool
    localMaterialOriginIsRecorded : Bool
    applicationContextIsFirstClass : Bool
    measuredOutcomesRequireEvidenceCarrier : Bool
    practiceIdentityAutomaticallyProvesMechanism : Bool
    localOriginAutomaticallyProvesBenefit : Bool
    knfAutomaticallyMeansZeroExternalInput : Bool
    oneStudyAutomaticallyGeneralisesAcrossSites : Bool

canonicalKoreanNaturalFarmingBoundary : KoreanNaturalFarmingBoundary
canonicalKoreanNaturalFarmingBoundary =
  korean-natural-farming-boundary
    true true true true true false false false false
