{-# OPTIONS --safe #-}
module DASHI.Physics.Propulsion.Rocketdyne1974IdentifiabilityCutExact where

open import DASHI.Core.Prelude using (⊥)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _*_)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- IDENTIFIABILITY CUT FOR THIN-SHELL PRESSURE STRESS
--
-- For a local thin-shell scaling sigma * t = p*r, pressure-radius load alone
-- does not identify stress when thickness t is absent.  The exact arithmetic
-- witnesses below make the non-uniqueness explicit without division.
------------------------------------------------------------------------

record ShellCandidate : Set where
  constructor shell-candidate
  field
    loadCode : Nat
    thicknessCode : Nat
    stressCode : Nat
    relation : thicknessCode * stressCode ≡ loadCode

candidateThin : ShellCandidate
candidateThin = shell-candidate 120 2 60 refl

candidateThick : ShellCandidate
candidateThick = shell-candidate 120 3 40 refl

twoThicknessesSameLoad :
  ShellCandidate.loadCode candidateThin ≡
  ShellCandidate.loadCode candidateThick
twoThicknessesSameLoad = refl

twoIsNotThree : 2 ≡ 3 → ⊥
twoIsNotThree ()

sixtyIsNotForty : 60 ≡ 40 → ⊥
sixtyIsNotForty ()

record NonUniqueStressWitness : Set where
  constructor non-unique-stress-witness
  field
    left : ShellCandidate
    right : ShellCandidate
    sameLoad : ShellCandidate.loadCode left ≡ ShellCandidate.loadCode right
    distinctThickness :
      ShellCandidate.thicknessCode left ≡ ShellCandidate.thicknessCode right → ⊥
    distinctStress :
      ShellCandidate.stressCode left ≡ ShellCandidate.stressCode right → ⊥

geometryFreeStressNotUnique : NonUniqueStressWitness
geometryFreeStressNotUnique =
  non-unique-stress-witness
    candidateThin candidateThick refl twoIsNotThree sixtyIsNotForty

------------------------------------------------------------------------
-- Thermal-stress identifiability has the same structure:
-- E * alpha * DeltaT depends on constitutive and boundary-condition inputs.
-- This owner records the exact remaining producer payments rather than
-- fabricating a stress value from the 2300 F thermocouple observation.
------------------------------------------------------------------------

record PhysicalMaxCut : Set where
  constructor physical-max-cut
  field
    exactWC103Identity : Bool
    exactVH101CoatingIdentity : Bool
    exactAreaRatioEndpoints : Bool
    exactLocalWallThickness : Bool
    exactLocalRadiusProfile : Bool
    timeResolvedWallTemperatureField : Bool
    calibratedHeatFluxField : Bool
    sameArticleHaynesStrengthCreepLaw : Bool
    sameArticleWC103StrengthCreepLaw : Bool
    loadAndConstraintBoundaryConditions : Bool
    calibratedTwoMaterialPrediction : Bool
    currentStoppingRule : String

currentPhysicalMaxCut : PhysicalMaxCut
currentPhysicalMaxCut =
  physical-max-cut
    true true true
    false false false false false false false false
    "Do not promote beyond empirical material-outcome discrimination until geometry + thermal field + constitutive laws close the stress/creep solve."

record IdentifiabilityBoundary : Set where
  constructor identifiability-boundary
  field
    pressureAndTemperatureAloneIdentifyFailureStress : Bool
    missingThicknessCanChangeInferredStress : Bool
    missingConstitutiveLawCanChangeFailureMargin : Bool
    nonidentifiabilityIsAValidScientificResult : Bool

canonicalIdentifiabilityBoundary : IdentifiabilityBoundary
canonicalIdentifiabilityBoundary =
  identifiability-boundary false true true true
