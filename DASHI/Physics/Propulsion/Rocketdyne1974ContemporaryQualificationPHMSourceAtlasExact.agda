{-# OPTIONS --safe #-}
module DASHI.Physics.Propulsion.Rocketdyne1974ContemporaryQualificationPHMSourceAtlasExact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- CONTEMPORARY SOURCE ATLAS — STRUCTURAL COMPARATORS ONLY
--
-- These sources illuminate modern qualification/PHM/model-credibility
-- coordinates. They do not retroactively impose modern standards on the 1974
-- Rocketdyne programme and do not supply historical same-object data.
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
    sourceReference : String

nasaSTD6030 : ContemporarySource
nasaSTD6030 = contemporary-source
  "NASA-STD-6030, Additive Manufacturing Requirements for Spaceflight Systems"
  2021 activeStandard
  "active NASA standard governing AM design/fabrication/testing qualification coordinates for spaceflight hardware"
  false false
  "modern qualification-grammar comparator only; does not apply retroactively to R-9557"
  "NASA Technical Standards System: https://standards.nasa.gov/node/2739"

nasaHDBK5026 : ContemporarySource
nasaHDBK5026 = contemporary-source
  "NASA-HDBK-5026, Guidance on Strength, Fatigue, and Fracture Control Requirements for Additively Manufactured Spaceflight Hardware"
  2024 handbook
  "links AM strength/fatigue/fracture-control implementation to structural, NDE, propulsion-life and fracture-control requirements"
  false false
  "supports keeping material/process, inspection, strength/life and acceptance coordinates separate"
  "NASA Technical Standards System: https://standards.nasa.gov/node/11897"

nasaSTD5023 : ContemporarySource
nasaSTD5023 = contemporary-source
  "NASA-STD-5023, Design and Verification Requirements for Spaceflight Valves"
  2026 activeStandard
  "uniform valve design/verification requirements motivated by requirement gaps and costly historical valve failures"
  false false
  "modern valve-qualification comparator; does not identify the Moog 54X107A historical failure population"
  "NASA Technical Standards System: https://standards.nasa.gov/standard/NASA/NASA-STD-5023"

nasaSTD5012C : ContemporarySource
nasaSTD5012C = contemporary-source
  "NASA-STD-5012C, Strength and Life Assessment Requirements for Liquid-Fueled Space Propulsion System Engines"
  2025 activeStandard
  "defines propulsion-engine structural life in fatigue/creep terms and requires analyses plus tests for structural qualification; hot-fire success alone is not the structural qualification argument"
  false false
  "supports separating observed firing survival from structural strength/life qualification; transfers no 1974 acceptance criterion"
  "NASA Technical Standards System node 250; C update dated 2025-12-31: https://standards.nasa.gov/node/250"

nasaSTD5009C : ContemporarySource
nasaSTD5009C = contemporary-source
  "NASA-STD-5009C, Nondestructive Evaluation Requirements for Fracture Critical Metallic Components"
  2023 activeStandard
  "requires quantitative probability-of-detection support where fracture control relies on NDE"
  false false
  "supports refining inspection from presence/absence to method, coverage, defect class, detection capability/POD and acceptance threshold"
  "NASA Technical Standards System: https://standards.nasa.gov/standard/nasa/nasa-std-5009"

nasaSTD5019AChange4 : ContemporarySource
nasaSTD5019AChange4 = contemporary-source
  "NASA-STD-5019A Change 4, Fracture Control Requirements for Spaceflight Hardware"
  2024 activeStandard
  "treats fracture control as a programme of design, analysis, testing, NDE and tracking of fracture-critical hardware under an approved fracture-control plan"
  false false
  "supports keeping defect state, inspection, article tracking and life disposition explicit; does not retroactively classify R-9557 hardware"
  "NASA Technical Standards System: https://standards.nasa.gov/node/253"

nasaSTD7009B : ContemporarySource
nasaSTD7009B = contemporary-source
  "NASA-STD-7009B, Standard for Models and Simulations"
  2024 activeStandard
  "establishes lifecycle modeling/simulation credibility practices including verification, validation, uncertainty and program-defined acceptance criteria"
  false false
  "supports an explicit model-credibility contract around reconstructed Test-052 physics; does not create historical model adequacy"
  "NASA Technical Standards System: https://standards.nasa.gov/standard/NASA/NASA-STD-7009"

nasaHDBK7009B : ContemporarySource
nasaHDBK7009B = contemporary-source
  "NASA-HDBK-7009B, NASA Handbook for Models and Simulations"
  2026 handbook
  "guides empirical validation against real-world referents across normal/off-design/test/non-operational environments and requires uncertainty to be understood"
  false false
  "supports freezing a validated declared-use model before extrapolating from Test 052 to Tests 768/870-2; no numerical Rocketdyne validation metric is supplied"
  "NASA Technical Standards System: https://standards.nasa.gov/standard/NASA/NASA-HDBK-7009"

raambo : ContemporarySource
raambo = contemporary-source
  "NASA TechPort 147003, RAMPT-RAAMBO"
  2026 projectReport
  "integrated computational-materials/design/build/test development of refractory alloys for high-temperature propulsion and related systems"
  false false
  "supports design-build-inspect-test/process-history grammar; transfers no Rocketdyne numerical result"
  "NASA TechPort project 147003: https://techport.nasa.gov/projects/147003"

c103HeatTreatment2025 : ContemporarySource
c103HeatTreatment2025 = contemporary-source
  "NASA NTRS 20250002623, Heat Treatment Optimization of L-PBF C103"
  2025 materialProcessStudy
  "HIP can improve C103 density while associated grain growth can reduce mechanical properties; heat-treatment path is a live material-state coordinate"
  false false
  "supports process-history dependence of C103 properties; cannot calibrate 1974 WC103/VH-101"
  "NASA NTRS 20250002623: https://ntrs.nasa.gov/citations/20250002623"

lreHealthMonitoring2026 : ContemporarySource
lreHealthMonitoring2026 = contemporary-source
  "Wu et al. 2026, Liquid-propellant rocket engine health monitoring technologies: A survey, insights, and prospects"
  2026 reviewArticle
  "reviews transition toward lifecycle health management, multimodal sensing, hybrid physics-data models and predictive maintenance; identifies data quality, generalization, interpretability and engineering validation challenges"
  false false
  "modern PHM architecture comparator only; does not provide a historical Rocketdyne failure-rate denominator"
  "Progress in Aerospace Sciences 166 (2026) 101251; DOI 10.1016/j.paerosci.2026.101251"

record ContemporarySourceAtlasBoundary : Set where
  constructor contemporary-source-atlas-boundary
  field
    modernQualificationGrammarRelevant : Bool
    processHistoryRelevant : Bool
    inspectionAndNDERelevant : Bool
    quantitativePODRelevant : Bool
    strengthLifeQualificationRelevant : Bool
    fractureControlTrackingRelevant : Bool
    modelCredibilityRelevant : Bool
    serviceHistoryAndPHMRelevant : Bool
    modernSourcesPay1974Geometry : Bool
    modernSourcesPay1974ConstitutiveLaw : Bool
    modernSourcesPay1974ReliabilityPopulation : Bool
    modernSourcesPay1974ValidationResidual : Bool
    modernStandardsApplyRetroactively : Bool
    boundary : String

contemporarySourceAtlasBoundary : ContemporarySourceAtlasBoundary
contemporarySourceAtlasBoundary = contemporary-source-atlas-boundary
  true true true true true true true true
  false false false false false
  "Contemporary sources guide acquisition, qualification and model-credibility structure only. Historical claims remain source-owned and same-object gated."

attributionFirewall : String
attributionFirewall =
  "NASA/author sources own reported requirements/results; DASHI owns only the formal crosswalk, acquisition routing, derived structural distinctions and non-promotion boundaries."
