{-# OPTIONS --safe #-}
module DASHI.Physics.Propulsion.Rocketdyne1974SiblingRCSComparisonExact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- CONTEMPORANEOUS SPACE-SHUTTLE RCS SIBLING COMPARATOR
------------------------------------------------------------------------

data CoolingArchitecture : Set where
  berylliumInteregen fuelVortexCooledColumbium : CoolingArchitecture

data ComparisonAuthority : Set where
  sameContractInterface independentSiblingReport laterDesignCriteria : ComparisonAuthority

record RCSProgrammeComparator : Set where
  constructor rcs-programme-comparator
  field
    programme : String
    contract : String
    nominalThrustLbf : Nat
    nominalChamberPressurePsia : Nat
    propellants : String
    coolingArchitecture : CoolingArchitecture
    reuseObjective : String
    reportedDemonstration : String
    relationshipToRocketdyne : String
    authority : ComparisonAuthority
    sameThrustChamber : Bool
    sourceReference : String

bellNAS912996Comparator : RCSProgrammeComparator
bellNAS912996Comparator =
  rcs-programme-comparator
    "Bell Aerospace Model 8701 Space Shuttle bipropellant RCS engine"
    "NAS9-12996"
    600 200
    "N2O4/MMH"
    fuelVortexCooledColumbium
    "100-mission reusable Shuttle RCS with minimum servicing"
    "reported ~295-s vacuum Isp; 9900 s operation including 6300 firing cycles without maintenance in the 1973 AIAA summary"
    "contemporaneous competing/sibling Shuttle-RCS technology programme; NASA/JSC supplied Rocketdyne Moog 54X107-series hardware originating under NAS9-12996"
    sameContractInterface
    false
    "NASA-CR-134336; NASA-CR-136021; AIAA 73-1312 / NTRS 19740028558; R-9557/R-9557-1 valve sections"

-- R-9557-1 identifies valve S/N 003 as residual NAS9-12996 hardware and R-9557
-- says the 54X107 design was developed by Moog for that contract. This pays
-- contract origin, but it does not by itself identify which Bell test article
-- previously carried S/N 003 or reconstruct the full prior exposure history.
valveContractOriginPaid : Bool
valveContractOriginPaid = true

exactBellEngineValveAssignmentPaid : Bool
exactBellEngineValveAssignmentPaid = false

record ArchitectureComparison : Set where
  constructor architecture-comparison
  field
    rocketdyneArchitecture : CoolingArchitecture
    bellArchitecture : CoolingArchitecture
    sameMissionClass : Bool
    samePropellantFamily : Bool
    sameNominalThrustClass : Bool
    sameNominalChamberPressure : Bool
    sameCoolingMechanism : Bool
    admissibleInference : String
    forbiddenInference : String

sameShuttleRequirementDifferentCoolingArchitecture : ArchitectureComparison
sameShuttleRequirementDifferentCoolingArchitecture =
  architecture-comparison
    berylliumInteregen fuelVortexCooledColumbium
    true true true true false
    "two contemporaneous programmes provide a natural architecture-level comparator for reusable hypergolic RCS qualification, maintenance and environmental robustness"
    "different architecture/programme evidence cannot be pooled as though it were one engine or one material-life population"

record EnvironmentalCycleComparator : Set where
  constructor environmental-cycle-comparator
  field
    bellReportedCycles : Nat
    rocketdyneReportedCycles : Nat
    commonExposureKinds : String
    bellPerformanceChangeReported : Bool
    directCycleCountComparisonIsReliabilityLaw : Bool
    sourceReference : String

bellEnvironmentalCycleComparator : EnvironmentalCycleComparator
bellEnvironmentalCycleComparator =
  environmental-cycle-comparator
    10 6
    "salt/salt-water, sand-and-dust, vibration, humidity plus hot-fire cycling"
    false false
    "NASA-CR-136021 / NTRS 19740002607; NASA-CR-140308 / R-9557"

record CoatingRelatedWork : Set where
  constructor coating-related-work
  field
    programme : String
    object : String
    purpose : String
    sameHistoricalRocketdyneNozzle : Bool
    sourceReference : String

bellCoatingDurabilityStudy : CoatingRelatedWork
bellCoatingDurabilityStudy =
  coating-related-work
    "Bell NAS9-12996"
    "high-temperature oxidation-resistant RCS thrust-chamber coating under fuel-vortex film cooling"
    "screen materials, fabricate chamber, generate engine firing data and evaluate coating durability"
    false
    "NASA-CR-141450 / Bell 8701-910045 / NTRS 19750005996"

record SiblingComparisonBoundary : Set where
  constructor sibling-comparison-boundary
  field
    sameShuttleRCSRequirementFamily : Bool
    commonContractValveInterfaceDocumented : Bool
    sameEngineProgramme : Bool
    sameCoolingArchitecture : Bool
    environmentalResultsDirectlyPoolable : Bool
    siblingCanActAsCounterfactualControl : Bool
    siblingCanGuideAcquisition : Bool
    boundary : String

siblingComparisonBoundary : SiblingComparisonBoundary
siblingComparisonBoundary =
  sibling-comparison-boundary
    true true false false false false true
    "Bell supplies a contemporaneous alternative architecture and shared Shuttle-RCS requirement/contract interface; it is related work and an acquisition guide, not a randomized control or same-object reliability population."

record SiblingAcquisitionFrontier : Set where
  constructor sibling-acquisition-frontier
  field
    exactMoogValveContractOrigin : Bool
    exactPriorBellArticleAssignment : Bool
    bellEnvironmentalProtocolRecovered : Bool
    bellValveFailureHistoryRecovered : Bool
    bellCoatingArticleDataRecovered : Bool
    commonNASARequirementMatrixRecovered : Bool
    nextSource : String

siblingAcquisitionFrontier : SiblingAcquisitionFrontier
siblingAcquisitionFrontier =
  sibling-acquisition-frontier
    true false false false false false
    "Contract origin is paid. Next acquire NAS9-12996 serial-level valve/test records, Bell environmental protocols and coating data, then compare component-by-component against R-9557 rather than comparing headline cycle counts."
