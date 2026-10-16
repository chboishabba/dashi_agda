{-# OPTIONS --safe #-}
module DASHI.Physics.Propulsion.Rocketdyne1974ContemporaryQualificationPHMSourceAtlasExact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- CONTEMPORARY SOURCE ATLAS — STRUCTURAL COMPARATORS ONLY
--
-- These sources illuminate modern qualification/PHM coordinates.  They do
-- not retroactively impose modern standards on the 1974 Rocketdyne programme
-- and do not supply historical same-object constitutive or reliability data.
------------------------------------------------------------------------

data SourceRole : Set where
  activeStandard handbook projectReport materialProcessStudy reviewArticle : SourceRole

record ContemporarySource : Set where
  constructor contemporary-source
  field
    sourceId : String
    year : Nat
    role : SourceRole
    boundedClaim : String
    rocketdyneSameObjectEvidence : Bool
    historicalRequirementAuthority : Bool
    admissibleTransfer : String

nasaSTD6030 : ContemporarySource
nasaSTD6030 = contemporary-source
  "NASA-STD-6030, Additive Manufacturing Requirements for Spaceflight Systems"
  2021 activeStandard
  "active NASA standard governing AM design/fabrication/testing qualification coordinates for spaceflight hardware"
  false false
  "modern qualification-grammar comparator only; does not apply retroactively to R-9557"

nasaHDBK5026 : ContemporarySource
nasaHDBK5026 = contemporary-source
  "NASA-HDBK-5026, Guidance on Strength, Fatigue, and Fracture Control Requirements for Additively Manufactured Spaceflight Hardware"
  2024 handbook
  "links AM strength/fatigue/fracture-control implementation to structural, NDE, propulsion-life and fracture-control requirements"
  false false
  "supports keeping material/process, inspection, strength/life and acceptance coordinates separate"

nasaSTD5023 : ContemporarySource
nasaSTD5023 = contemporary-source
  "NASA-STD-5023, Design and Verification Requirements for Spaceflight Valves"
  2026 activeStandard
  "uniform valve design/verification requirements motivated by requirement gaps and costly historical valve failures"
  false false
  "modern valve-qualification comparator; does not identify the Moog 54X107A historical failure population"

raambo : ContemporarySource
raambo = contemporary-source
  "NASA TechPort 147003, RAMPT-RAAMBO"
  2026 projectReport
  "integrated computational-materials/design/build/test development of refractory alloys for high-temperature propulsion and related systems"
  false false
  "supports design-build-inspect-test/process-history grammar; transfers no Rocketdyne numerical result"

c103HeatTreatment2025 : ContemporarySource
c103HeatTreatment2025 = contemporary-source
  "NASA NTRS 20250002623, Heat Treatment Optimization of L-PBF C103"
  2025 materialProcessStudy
  "HIP can improve C103 density while associated grain growth can reduce mechanical properties; heat-treatment path is a live material-state coordinate"
  false false
  "supports process-history dependence of C103 properties; cannot calibrate 1974 WC103/VH-101"

lreHealthMonitoring2026 : ContemporarySource
lreHealthMonitoring2026 = contemporary-source
  "Wu et al. 2026, Liquid-propellant rocket engine health monitoring technologies: A survey, insights, and prospects"
  2026 reviewArticle
  "reviews transition toward lifecycle health management, multimodal sensing, hybrid physics-data models and predictive maintenance; identifies data quality, generalization, interpretability and engineering validation challenges"
  false false
  "modern PHM architecture comparator only; does not provide a historical Rocketdyne failure-rate denominator"

record ContemporarySourceAtlasBoundary : Set where
  constructor contemporary-source-atlas-boundary
  field
    modernQualificationGrammarRelevant : Bool
    processHistoryRelevant : Bool
    inspectionAndNDERelevant : Bool
    serviceHistoryAndPHMRelevant : Bool
    modernSourcesPay1974Geometry : Bool
    modernSourcesPay1974ConstitutiveLaw : Bool
    modernSourcesPay1974ReliabilityPopulation : Bool
    modernStandardsApplyRetroactively : Bool
    boundary : String

contemporarySourceAtlasBoundary : ContemporarySourceAtlasBoundary
contemporarySourceAtlasBoundary = contemporary-source-atlas-boundary
  true true true true
  false false false false
  "Contemporary sources guide acquisition/model structure only. Historical claims remain source-owned and same-object gated."

attributionFirewall : String
attributionFirewall =
  "NASA/author sources own reported requirements/results; DASHI owns only the formal crosswalk, acquisition routing and non-promotion boundaries."
