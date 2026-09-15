module DASHI.Wikimedia.IbrahimCannabisTobaccoCoAdministrationDesignPrecedentExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Wikimedia.IbrahimCannabisTobaccoThreeArmExecutionExact as ThreeArm

------------------------------------------------------------------------
-- DIRECT HUMAN CO-ADMINISTRATION DESIGN PRECEDENT
------------------------------------------------------------------------

record ThreeArmHumanPrecedent : Set where
  constructor three-arm-human-precedent
  field
    sourceLabel : String
    doi : String
    publicationYear : Nat
    participantCount : Nat
    withinSubject : Bool
    cannabisOnlyArm : Bool
    tobaccoOnlyArm : Bool
    mixedArm : Bool
    mixtureRatio : String
    standardizedPuffs : Nat
    device : String
    primaryExposureFindings : String
    pesticideChemistryMeasured : Bool
open ThreeArmHumanPrecedent public

stHelen2025 : ThreeArmHumanPrecedent
stHelen2025 = three-arm-human-precedent
  "St Helen et al. 2025 loose-leaf vaporizer proof-of-concept"
  "10.1016/j.drugalcdep.2025.112678"
  2025 8 true true true true "50:50 cannabis:tobacco" 3 "PAX-3 loose-leaf vaporizer"
  "mixed co-administration produced higher plasma THC exposure than cannabis alone and higher plasma nicotine exposure than tobacco alone in this small proof-of-concept"
  false

------------------------------------------------------------------------
-- ACTIVE FOLLOW-ON PROGRAM
------------------------------------------------------------------------

record ActiveClinicalProgram : Set where
  constructor active-clinical-program
  field
    registryId : String
    officialTitle : String
    sponsor : String
    status : String
    lastUpdate : String
    estimatedEnrollment : Nat
    studyStart : String
    estimatedCompletion : String
    randomized : Bool
    doubleBlinded : Bool
    crossover : Bool
    studyConditions : Nat
    standardizedPuffs : Nat
    device : String
    resultsPosted : Bool
    contaminantResiduesMeasured : Bool
open ActiveClinicalProgram public

cannic2026 : ActiveClinicalProgram
cannic2026 = active-clinical-program
  "NCT05999383"
  "Understanding the Clinical Pharmacology of Marijuana-Tobacco Co-administration"
  "University of California, San Francisco"
  "Recruiting"
  "2026-01-07"
  48
  "2025-07-01"
  "2028-02-01"
  true true true 8 5 "PAX-3 loose-leaf vaporizer"
  false false

------------------------------------------------------------------------
-- CROSS-POLLINATION TO THE PESTICIDE TRANSFER EXPERIMENT
------------------------------------------------------------------------

record DesignTransfer : Set where
  constructor design-transfer
  field
    sourceDesign : String
    retainedPrimitive : String
    targetDesign : String
    sameScientificConsumer : Bool
    sameChemicalEndpoint : Bool
    transferNeedsNewMeasurement : Bool
open DesignTransfer public

threeArmPrimitiveTransfer : DesignTransfer
threeArmPrimitiveTransfer = design-transfer
  "2025 human cannabis-only / tobacco-only / 50:50 mixed PAX-3 crossover"
  "three-arm same-session comparison with standardized administration"
  "same-source cannabis-only / tobacco-only / mixed combustion pesticide-transfer experiment"
  false false true

------------------------------------------------------------------------
-- The precedent supports experimental architecture, not residue conclusions.
------------------------------------------------------------------------

data PKInteractionCreatesPesticideInteraction : Set where
data VaporizerResultCreatesCombustionResult : Set where
data FiftyFiftyCreatesUniversalSpliffRatio : Set where
data RecruitingTrialCreatesPublishedResult : Set where

pkDoesNotCreatePesticideInteraction : PKInteractionCreatesPesticideInteraction → ⊥
pkDoesNotCreatePesticideInteraction ()

vapeDoesNotCreateCombustion : VaporizerResultCreatesCombustionResult → ⊥
vapeDoesNotCreateCombustion ()

fiftyFiftyNotUniversal : FiftyFiftyCreatesUniversalSpliffRatio → ⊥
fiftyFiftyNotUniversal ()

recruitingDoesNotCreateResult : RecruitingTrialCreatesPublishedResult → ⊥
recruitingDoesNotCreateResult ()

record CoAdministrationPrecedentBoundary : Set where
  constructor co-administration-precedent-boundary
  field
    directThreeArmHumanPrecedentPaid : Bool
    mixedExposureNontrivialityObserved : Bool
    directPesticideInteractionPaid : Bool
    combustionIdentityPaid : Bool
    activeFollowOnProgramPaid : Bool
    activeProgramResultsPaid : Bool
open CoAdministrationPrecedentBoundary public

canonicalCoAdministrationPrecedentBoundary : CoAdministrationPrecedentBoundary
canonicalCoAdministrationPrecedentBoundary =
  co-administration-precedent-boundary true true false false true false
