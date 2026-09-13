module DASHI.Physics.Materials.FangDainingActiveMechanicalMetamaterialBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- FANG DAINING / ACTIVE MECHANICAL METAMATERIALS
--
-- Source-shaped owner from Beijing Institute of Technology institutional pages.
-- This is ordinary published materials/structure mechanics.  It is not evidence
-- of recovered craft, S4 provenance, or non-human manufacture.
------------------------------------------------------------------------

data ConstructionPrinciple : Set where
  phaseTransition strainMismatch mechanicalInstability : ConstructionPrinciple

data StimulusField : Set where
  temperature chemical light electric magnetic pressure : StimulusField

record ActiveMechanicalMetamaterialScience : Set where
  constructor active-mechanical-metamaterial-science
  field
    scientist : String
    institution : String
    object : String
    constructionPrinciples : List ConstructionPrinciple
    stimulusFields : List StimulusField
    multiscaleMultiphysics : Bool
    activeSenseResponse : Bool
    sourceReference : String
    sourceClass : String
    boundedReading : String

open ActiveMechanicalMetamaterialScience public

fangActiveMechanicalMetamaterials : ActiveMechanicalMetamaterialScience
fangActiveMechanicalMetamaterials = active-mechanical-metamaterial-science
  "Fang Daining"
  "Beijing Institute of Technology, Institute of Advanced Structure Technology"
  "active mechanical metamaterials / intelligent driven mechanical advanced structures"
  (phaseTransition ∷ strainMismatch ∷ mechanicalInstability ∷ [])
  (temperature ∷ chemical ∷ light ∷ electric ∷ magnetic ∷ pressure ∷ [])
  true true
  "BIT Institute of Advanced Structure Technology, 2021-11-09 review of Active Mechanical Metamaterials; Fang/Li team"
  "primary institutional research page"
  "The institutional source describes artificially designed microstructure, stimulus-responsive materials and phase-transition/strain-mismatch/instability construction principles. It pays metamaterial science, not reverse-engineered extraterrestrial provenance."

record ExtremeEnvironmentMaterialsScience : Set where
  constructor extreme-environment-materials-science
  field
    scientist : String
    testEnvironment : String
    measuredProperties : String
    equipment : String
    aerospaceDefenceApplication : Bool
    sourceReference : String

open ExtremeEnvironmentMaterialsScience public

fangUltraHighTemperatureTesting : ExtremeEnvironmentMaterialsScience
fangUltraHighTemperatureTesting = extreme-environment-materials-science
  "Fang Daining"
  "oxidising 1800 C; inert 2300 C; multi-atmosphere high-temperature regimes"
  "tension, bending, compression, shear, oxidation and thermal-shock response"
  "institutionally described ultra-high-temperature mechanical/material test systems"
  true
  "BIT Institute of Advanced Structure Technology, 2016-06-07 ultra-high-temperature extreme-environment testing progress"

record FangMetamaterialBoundary : Set where
  constructor fang-metamaterial-boundary
  field
    metamaterialMeansExtraterrestrialMaterial : Bool
    unusualEffectivePropertyImpliesUnknownProvenance : Bool
    defenceApplicationImpliesArea51 : Bool
    publishedMetamaterialScienceMayTestConspiracyMaterialClaims : Bool
    exactMaterialProvenanceStillRequired : Bool

canonicalFangMetamaterialBoundary : FangMetamaterialBoundary
canonicalFangMetamaterialBoundary = fang-metamaterial-boundary
  false false false true true
