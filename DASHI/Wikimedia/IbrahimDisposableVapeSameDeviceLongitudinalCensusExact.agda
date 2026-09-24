module DASHI.Wikimedia.IbrahimDisposableVapeSameDeviceLongitudinalCensusExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Wikimedia.IbrahimDisposableVapeChemicalCensusExperimentExact as Census
import DASHI.Wikimedia.IbrahimDisposableVapeUnknownFeatureLedgerExact as Ledger
import DASHI.Wikimedia.IbrahimDisposableVapeChemicalUniverseObserverParetoExact as Observer

------------------------------------------------------------------------
-- SAME-DEVICE LONGITUDINAL CENSUS
--
-- Consumer:
--   how does the chemical system delivered by one physical disposable evolve
--   over its actual operating life?
--
-- Cross-sectional used-versus-new studies remain valuable acquisition priors,
-- but they do not substitute for a stage-indexed trajectory of one specimen.
------------------------------------------------------------------------

data LongitudinalStage : Set where
  unopened : LongitudinalStage
  virginBaseline : LongitudinalStage
  puff100 : LongitudinalStage
  puff200 : LongitudinalStage
  puff300 : LongitudinalStage
  puff500 : LongitudinalStage
  midLife : LongitudinalStage
  lateLife : LongitudinalStage
  exhaustedOrStop : LongitudinalStage
  spentMaterials : LongitudinalStage

record PhysicalSpecimen : Set where
  constructor physical-specimen
  field
    specimenId : String
    brand : String
    model : String
    flavour : String
    labelledPuffCapacity : String
    lotOrBatch : String
    acquisitionChannel : String
    jurisdiction : String
    packageIdentityReceipt : String
    samePhysicalDeviceAcrossStages : Bool
open PhysicalSpecimen public

record StageReceipt : Set where
  constructor stage-receipt
  field
    specimenId : String
    stage : LongitudinalStage
    cumulativePuffs : Nat
    liquidSampleTaken : Bool
    aerosolSampleTaken : Bool
    nonTargetOrganic : Bool
    targetedCarbonyls : Bool
    aerosolMetals : Bool
    deviceMassOrLiquidMass : String
    powerOrFlowReceipt : String
    featureMapReceipt : String
    destructiveStage : Bool
open StageReceipt public

------------------------------------------------------------------------
-- SOURCE-BOUNDED ACQUISITION PRECEDENTS
------------------------------------------------------------------------

record LongitudinalSourceReceipt : Set where
  constructor longitudinal-source-receipt
  field
    sourceLabel : String
    doi : String
    specimenScope : String
    repeatedSameDevicePaid : Bool
    repeatedStageDefinition : String
    supportedClaim : String
    excludedPromotion : String
open LongitudinalSourceReceipt public

metalsLifeCycle2025 : LongitudinalSourceReceipt
metalsLifeCycle2025 = longitudinal-source-receipt
  "Elevated Toxic Element Emissions from Popular Disposable E-Cigarettes: Sources, Life Cycle, and Health Risks"
  "10.1021/acscentsci.5c00641"
  "ELF Bar BC5000, Flum Pebble 6000, Esco Bar 2500; selected single devices followed over life plus replicate product analyses"
  true
  "aerosol collected at 100-puff intervals; selected ELF Bar/Flum devices followed to 1300-1500 puffs, Esco Bar restricted by device failure; aged e-liquid sampled after use"
  "Cr and Ni aerosol concentrations changed strongly with puff count; device-material composition and aged e-liquid helped attribute several metal sources"
  "puff-resolved metal trajectory does not create puff-resolved organic/non-target trajectory"

highPuffAldehyde2026 : LongitudinalSourceReceipt
highPuffAldehyde2026 = longitudinal-source-receipt
  "Omaiye et al. Methylglyoxal and Glyoxal in High-Puff Disposable Electronic Cigarette Liquids"
  "10.1021/acsomega.5c13033"
  "77 used high-puff devices across 20 brands with unvaped comparison products"
  false
  "used versus unvaped groups; not one physical device followed from baseline"
  "MGO, glyoxal and formaldehyde increased in vaped fluids; glyceraldehyde and dihydroxyacetone occurred only in vaped comparison fluids; broad targeted flavour/coolant/nicotine/solvent panel retained"
  "cross-sectional used/unvaped comparison cannot establish the exact same-device stage trajectory"

------------------------------------------------------------------------
-- EXPERIMENTAL STAGE POLICY
------------------------------------------------------------------------

record StagePolicy : Set where
  constructor stage-policy
  field
    earlyRule : String
    midRule : String
    lateRule : String
    failureRule : String
    absolutePuffCountRetained : Bool
    fractionOfAdvertisedLifeRetained : Bool
    advertisedPuffCountTreatedAsTruth : Bool
open StagePolicy public

canonicalStagePolicy : StagePolicy
canonicalStagePolicy = stage-policy
  "collect early aerosol at 100 and 200 cumulative puffs where device function permits; retain exact puff count"
  "predeclare mid-life by measured delivered-aerosol/liquid depletion fraction plus exact puff count, not label claim alone"
  "sample late life before dry-hit / unstable-output exclusion boundary; retain exact puff count and remaining-liquid/device-mass receipt"
  "if device fails early, stop trajectory at observed failure and preserve failure as an outcome rather than extrapolating to labelled capacity"
  true true false

------------------------------------------------------------------------
-- PAIRED OBSERVATION PACKET
------------------------------------------------------------------------

record PairedStageObserver : Set where
  constructor paired-stage-observer
  field
    liquidOrganicTargeted : String
    liquidOrganicNonTarget : String
    aerosolOrganicTargeted : String
    aerosolOrganicNonTarget : String
    carbonylLane : String
    elementalLane : String
    materialsLane : String
    physicalOutputLane : String
    unknownFeaturesRetained : Bool
open PairedStageObserver public

canonicalPairedStageObserver : PairedStageObserver
canonicalPairedStageObserver = paired-stage-observer
  "quantitative nicotine, PG/VG, organic acids, coolants, recurrent flavourants and known reaction products"
  "GC-HRMS + LC-HRMS blank-subtracted feature map with unresolved features retained"
  "same confirmed targets in generated aerosol where method/matrix supports them"
  "gas/particle non-target feature map; stage correspondence requires orthogonal evidence"
  "dedicated aldehyde/carbonyl assay including MGO, glyoxal, formaldehyde, acetaldehyde, acrolein, glyceraldehyde and dihydroxyacetone where validated"
  "ICP-MS/elemental aerosol lane for Cr, Ni, Pb, Cu, Zn, Sb and other validated elements"
  "post-life coil/wick/sheath/contact/solder composition and corrosion-state analysis"
  "aerosol mass per block, puff count, draw/power metadata, remaining-liquid/device mass"
  true

------------------------------------------------------------------------
-- FEATURE CORRESPONDENCE ACROSS STAGES
------------------------------------------------------------------------

data CorrespondenceGrade : Set where
  sameFeatureUnpaid : CorrespondenceGrade
  massOrSpectrumCandidate : CorrespondenceGrade
  orthogonallySupported : CorrespondenceGrade
  standardConfirmedSameChemical : CorrespondenceGrade

record LongitudinalFeature : Set where
  constructor longitudinal-feature
  field
    specimenId : String
    featureKey : String
    firstStage : LongitudinalStage
    laterStage : LongitudinalStage
    correspondenceGrade : CorrespondenceGrade
    firstAbundance : String
    laterAbundance : String
    direction : String
    interpretation : String
open LongitudinalFeature public

record StageResiduals : Set where
  constructor stage-residuals
  field
    liquidDrift : String
    aerosolDrift : String
    emissionResidual : String
    materialAttributionResidual : String
    unknownFeatureEmergence : String
open StageResiduals public

canonicalStageResiduals : StageResiduals
canonicalStageResiduals = stage-residuals
  "R_liquid(t2,t1) = stage-normalized liquid feature map at t2 minus t1"
  "R_aerosol(t2,t1) = per-puff or per-aerosol-mass feature/yield map at t2 minus t1"
  "R_emit(t) = aerosol inventory at t minus paired source-liquid inventory at t, preserving phase/matrix semantics"
  "R_material = aerosol-only or increasing element/feature pattern minus what source liquid alone can explain, joined to device-material evidence"
  "U_new(t2,t1) = reproducible blank-subtracted features first appearing after use; identity may remain unpaid"

------------------------------------------------------------------------
-- EXISTING EVIDENCE -> NEW EXPERIMENT REPAIR
------------------------------------------------------------------------

record LongitudinalRepair : Set where
  constructor longitudinal-repair
  field
    coarseEvidence : String
    defect : String
    refinement : String
    consumerAfterRepair : String
open LongitudinalRepair public

canonicalLongitudinalRepair : LongitudinalRepair
canonicalLongitudinalRepair = longitudinal-repair
  "cross-sectional new/used chemistry plus puff-resolved metals from separate studies"
  "organic chemistry, metals and source attribution are not observed as one synchronized same-device trajectory"
  "follow one physical specimen through stage-indexed paired liquid+aerosol observations and finish with materials analysis"
  "stage-specific chemical delivery and origin hypotheses can be tested without erasing specimen identity"

------------------------------------------------------------------------
-- HARD FIREWALLS
------------------------------------------------------------------------

data LabelledPuffCapacityCreatesObservedLife : Set where
data CrossSectionCreatesSameDeviceTrajectory : Set where
data SameExactMassCreatesSameChemicalAcrossStages : Set where
data PuffResolvedMetalsCreatePuffResolvedOrganics : Set where
data UsedLiquidIncreaseCreatesAerosolDoseIncrease : Set where
data OneLongitudinalDeviceCreatesPopulationDistribution : Set where

labelNotObservedLife : LabelledPuffCapacityCreatesObservedLife → ⊥
labelNotObservedLife ()

crossSectionNotLongitudinal : CrossSectionCreatesSameDeviceTrajectory → ⊥
crossSectionNotLongitudinal ()

massNotSameChemical : SameExactMassCreatesSameChemicalAcrossStages → ⊥
massNotSameChemical ()

metalTrajectoryNotOrganicTrajectory : PuffResolvedMetalsCreatePuffResolvedOrganics → ⊥
metalTrajectoryNotOrganicTrajectory ()

liquidIncreaseNotDoseIncrease : UsedLiquidIncreaseCreatesAerosolDoseIncrease → ⊥
liquidIncreaseNotDoseIncrease ()

oneDeviceNotPopulation : OneLongitudinalDeviceCreatesPopulationDistribution → ⊥
oneDeviceNotPopulation ()

record SameDeviceLongitudinalBoundary : Set where
  constructor same-device-longitudinal-boundary
  field
    puffResolvedMetalPrecedentPaid : Bool
    crossSectionalOrganicAgingPaid : Bool
    sameDeviceStageArchitecturePaid : Bool
    unknownFeatureCorrespondenceTyped : Bool
    pairedLiquidAerosolPacketPaid : Bool
    sameDeviceOrganicNonTargetPublicReceiptPaid : Bool
    physicalExecutionPaid : Bool
open SameDeviceLongitudinalBoundary public

canonicalSameDeviceLongitudinalBoundary : SameDeviceLongitudinalBoundary
canonicalSameDeviceLongitudinalBoundary = same-device-longitudinal-boundary
  true true true true true false false
