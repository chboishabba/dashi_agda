module DASHI.Wikimedia.IbrahimDisposableVapeLongitudinalAcquisitionExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Wikimedia.IbrahimDisposableVapeSameDeviceLongitudinalCensusExact as Longitudinal

------------------------------------------------------------------------
-- ACQUISITION FRONTIER
--
-- Target public receipt must satisfy all four gates simultaneously:
--   same physical disposable
--   puff/stage resolved
--   emitted aerosol
--   broad organic non-target discovery
--
-- Near misses are retained explicitly rather than promoted.
------------------------------------------------------------------------

record AcquisitionGate : Set where
  constructor acquisition-gate
  field
    samePhysicalDevice : Bool
    puffOrStageResolved : Bool
    aerosolObserved : Bool
    broadOrganicNonTarget : Bool
open AcquisitionGate public

record AcquisitionReceipt : Set where
  constructor acquisition-receipt
  field
    sourceLabel : String
    doiOrLocator : String
    deviceScope : String
    analyticalScope : String
    gate : AcquisitionGate
    supportedClaim : String
    unpaidCoordinate : String
open AcquisitionReceipt public

metalsLifeCycle2025 : AcquisitionReceipt
metalsLifeCycle2025 = acquisition-receipt
  "Elevated Toxic Element Emissions from Popular Disposable E-Cigarettes: Sources, Life Cycle, and Health Risks"
  "10.1021/acscentsci.5c00641"
  "ELF Bar BC5000 / Flum Pebble / Esco Bar disposables; selected single devices followed over life"
  "100-puff-block aerosol elemental analysis plus virgin/aged liquid and device-material analysis"
  (acquisition-gate true true true false)
  "direct same-device puff-resolved aerosol trajectory is paid for metals/materials"
  "does not provide broad organic non-target aerosol feature discovery"

puffResolvedGasPhase2021 : AcquisitionReceipt
puffResolvedGasPhase2021 = acquisition-receipt
  "Heide et al. Puff-Resolved Analysis and Selected Quantification of Chemicals in the Gas Phase of E-Cigarettes, Heat-Not-Burn Devices, and Conventional Cigarettes"
  "10.1093/ntr/ntab091"
  "ENDS/alternative nicotine devices compared with cigarette smoke"
  "online SPI-TOFMS coupled to a smoking machine for puff-resolved gas-phase chemical signals"
  (acquisition-gate true true true false)
  "demonstrates that online puff-resolved organic/gas-phase chemical observation is technically feasible"
  "not a modern disposable-bar same-device broad non-target life-cycle census; selected quantification/older device scope"

podLifeTargeted2023 : AcquisitionReceipt
podLifeTargeted2023 = acquisition-receipt
  "Jameson et al. Determination of chemical constituent yields in e-cigarette aerosol using partial and whole pod collections, a comparative analysis"
  "10.3389/fchem.2023.1223967"
  "JUUL, MyBlu, NJoy Ace and Vuse Alto closed systems"
  "beginning / middle / end puff-block aerosol measurements of primary constituents, metals, selected carbonyls and glycidol"
  (acquisition-gate true true true false)
  "targeted constituent yields can vary strongly over product life; early blocks can under-report later carbonyl/glycidol yields"
  "closed pod systems rather than modern disposable bars; targeted chemistry rather than broad non-target organics"

breezeProEOL2025 : AcquisitionReceipt
breezeProEOL2025 = acquisition-receipt
  "Liu. Comprehensive end-of-life characterization of five Breeze Pro disposable ENDS"
  "CORESTA PSPT 2025 STPOST 24"
  "Breeze Pro 5% nicotine disposables across five flavours"
  "50-puff EOL determination and 100-puff aerosol blocks for primary constituents, carbonyls and metals"
  (acquisition-gate true true true false)
  "same-device/end-of-life targeted disposable aerosol chemistry can be collected across full depletion"
  "conference poster, not peer-reviewed; no broad non-target organic feature map"

pairedNonTarget2021 : AcquisitionReceipt
pairedNonTarget2021 = acquisition-receipt
  "Characterizing the Chemical Landscape in Commercial E-Cigarette Liquids and Aerosols by LC-HRMS"
  "10.1021/acs.chemrestox.1c00253"
  "four commercial products including one disposable"
  "paired liquid/aerosol non-target LC-HRMS and chemical fingerprinting"
  (acquisition-gate false false true true)
  "broad non-target aerosol discovery is paid and additional aerosol compounds can appear beyond source liquid"
  "not a puff-resolved same-device longitudinal disposable trajectory"

popularDisposables2025 : AcquisitionReceipt
popularDisposables2025 = acquisition-receipt
  "Robertson et al. E-Liquid and Aerosol Characterization of Popular Disposable E-Cigarettes"
  "10.1021/acsomega.5c03167"
  "Flum Pebble / Elf Bar / Esco Bars / Geek Bar disposables"
  "liquid GC/MS and LC accurate-mass chemistry plus generated-aerosol carbonyls"
  (acquisition-gate true false true false)
  "modern bar-type disposable liquid chemistry and aerosol carbonyl emission are directly observed"
  "single/fixed collection regime rather than puff-resolved life cycle; no broad non-target aerosol feature census"

------------------------------------------------------------------------
-- EXACT PUBLIC-RECEIPT STATUS
------------------------------------------------------------------------

record FourGateStatus : Set where
  constructor four-gate-status
  field
    targetDescription : String
    publicReceiptLocated : Bool
    searchBound : String
    closestCoverage : String
    residual : String
open FourGateStatus public

currentFourGateStatus : FourGateStatus
currentFourGateStatus = four-gate-status
  "same physical modern disposable + puff/stage-resolved emitted aerosol + broad organic non-target discovery"
  false
  "public web / PubMed / PMC / ACS / publisher searches performed through 2026-09-15 using disposable, puff-resolved, same-device, aerosol, GC-MS/HRMS/non-target terms"
  "metals life-cycle pays same-device+puff-resolved; 2021 LC-HRMS pays broad non-target aerosol; targeted pod/disposable EOL studies pay stage-resolved selected constituents"
  "the conjunction of all four gates remains not located; not-located is not a proof of nonexistence"

------------------------------------------------------------------------
-- EXPERIMENTAL CROSS-POLLINATION
------------------------------------------------------------------------

record AcquisitionRepair : Set where
  constructor acquisition-repair
  field
    availablePrimitive1 : String
    availablePrimitive2 : String
    availablePrimitive3 : String
    missingWeld : String
open AcquisitionRepair public

canonicalAcquisitionRepair : AcquisitionRepair
canonicalAcquisitionRepair = acquisition-repair
  "100-puff same-device disposable life-cycle collection from the metals literature"
  "broad paired liquid/aerosol LC-HRMS non-target fingerprinting from chemical-landscape work"
  "dedicated short-block carbonyl collection because reactive carbonyls can be unstable over large pooled blocks"
  "apply all three to the same identified disposable across early/mid/late life while preserving specimen and feature identity"

------------------------------------------------------------------------
-- FIREWALLS
------------------------------------------------------------------------

data NearMissCreatesFourGateReceipt : Set where
data TargetedLifeCycleCreatesNonTargetLifeCycle : Set where
data NonTargetSingleStageCreatesLongitudinalTrajectory : Set where
data NotLocatedCreatesNonexistent : Set where

nearMissNotReceipt : NearMissCreatesFourGateReceipt → ⊥
nearMissNotReceipt ()

targetedNotNonTarget : TargetedLifeCycleCreatesNonTargetLifeCycle → ⊥
targetedNotNonTarget ()

singleStageNotLongitudinal : NonTargetSingleStageCreatesLongitudinalTrajectory → ⊥
singleStageNotLongitudinal ()

notLocatedNotNonexistent : NotLocatedCreatesNonexistent → ⊥
notLocatedNotNonexistent ()

record LongitudinalAcquisitionBoundary : Set where
  constructor longitudinal-acquisition-boundary
  field
    sameDevicePuffResolvedMetalsPaid : Bool
    sameDevicePuffResolvedTargetedOrganicPaid : Bool
    aerosolBroadNonTargetPaid : Bool
    modernDisposableTargetedAerosolPaid : Bool
    exactFourGatePublicReceiptPaid : Bool
    experimentWeldSpecified : Bool
open LongitudinalAcquisitionBoundary public

canonicalLongitudinalAcquisitionBoundary : LongitudinalAcquisitionBoundary
canonicalLongitudinalAcquisitionBoundary = longitudinal-acquisition-boundary
  true true true true false true
