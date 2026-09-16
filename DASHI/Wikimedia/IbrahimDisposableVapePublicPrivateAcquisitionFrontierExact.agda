module DASHI.Wikimedia.IbrahimDisposableVapePublicPrivateAcquisitionFrontierExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Wikimedia.IbrahimDisposableVapeSameDeviceLongitudinalCensusExact as Longitudinal

------------------------------------------------------------------------
-- PUBLIC / PRIVATE ACQUISITION FRONTIER
--
-- Exact public target:
--   same physical disposable × puff/stage resolved × aerosol observed ×
--   broad organic non-target chemistry.
--
-- A near miss pays only the gates it actually observes.  Failure to locate a
-- public receipt is not promoted to a claim that the experiment was never run.
------------------------------------------------------------------------

record FourGateReceipt : Set where
  constructor four-gate-receipt
  field
    sourceLabel : String
    sourceKind : String
    publicSurface : String
    samePhysicalDevice : Bool
    puffOrStageResolved : Bool
    aerosolObserved : Bool
    broadOrganicNonTarget : Bool
    disposableSpecific : Bool
    supports : String
    excludedPromotion : String
open FourGateReceipt public

metalsLifeCycle2025 : FourGateReceipt
metalsLifeCycle2025 = four-gate-receipt
  "Elevated Toxic Element Emissions from Popular Disposable E-Cigarettes"
  "peer-reviewed article"
  "ACS Central Science / PMC"
  true true true false true
  "same disposable devices followed through 100-puff aerosol blocks; aged liquid and internal materials measured"
  "elemental ICP-MS life-cycle data do not create broad organic non-target trajectories"

breezeProEOL2025 : FourGateReceipt
breezeProEOL2025 = four-gate-receipt
  "Comprehensive end-of-life characterization of Breeze Pro"
  "CORESTA conference abstract/poster"
  "CORESTA public abstract"
  true true true false true
  "selected constituents measured in 100-puff blocks through observed end-of-life"
  "conference surface is not a peer-reviewed broad non-target organic census"

puffResolvedOnlineMS2021 : FourGateReceipt
puffResolvedOnlineMS2021 = four-gate-receipt
  "Puff-resolved online gas-phase mass spectrometry of alternative nicotine delivery aerosols"
  "peer-reviewed method/application study"
  "PubMed-indexed public article"
  true true true true false
  "demonstrates puff-by-puff online chemical observation with broad gas-phase mass-spectral information"
  "not a modern disposable-bar whole-life same-device census"

commercialNonTarget2021 : FourGateReceipt
commercialNonTarget2021 = four-gate-receipt
  "Characterizing the Chemical Landscape in Commercial E-Cigarette Liquids and Aerosols by LC-HRMS"
  "peer-reviewed article"
  "public article / PMC"
  false false true true false
  "paired liquid/aerosol broad non-target feature discovery; extra aerosol features and unexpected compounds observed"
  "not a puff-resolved same-device disposable life-cycle trajectory"

popularDisposable2025 : FourGateReceipt
popularDisposable2025 = four-gate-receipt
  "E-Liquid and Aerosol Characterization of Popular Disposable E-Cigarettes"
  "peer-reviewed article"
  "ACS Omega / PMC"
  false false true false true
  "Flum Pebble, Elf Bar, Esco Bar and Geek Bar liquid chemistry plus aerosol carbonyls and aerosol mass"
  "targeted/semistructured aerosol chemistry does not create broad non-target whole-life coverage"

------------------------------------------------------------------------
-- REGULATORY / APPLICATION SIDE
------------------------------------------------------------------------

record RegulatoryAcquisitionReceipt : Set where
  constructor regulatory-acquisition-receipt
  field
    sourceLabel : String
    publicDocument : String
    nonTargetScreeningPerformed : Bool
    aerosolConstituentsOutsideTargetListObserved : Bool
    underlyingRawDatasetPubliclyAvailable : Bool
    disposableSpecificPaid : Bool
    puffResolvedWholeLifePaid : Bool
    interpretation : String
open RegulatoryAcquisitionReceipt public

fdaTPLNonTargetReceipt : RegulatoryAcquisitionReceipt
fdaTPLNonTargetReceipt = regulatory-acquisition-receipt
  "FDA Technical Project Lead review reporting applicant non-targeted differential screening"
  "FDA TPL review PDF"
  true true false false false
  "public FDA review documents prove that applicant-side non-target aerosol screening can exist inside tobacco-product applications; the public review is not the underlying full dataset and does not pay the disposable whole-life target"

record ManufacturingInformationLane : Set where
  constructor manufacturing-information-lane
  field
    surface : String
    ingredientSupplierInformationMayAppear : Bool
    analyticalMethodsMayAppear : Bool
    stabilityInformationMayAppear : Bool
    publicCompletenessPaid : Bool
open ManufacturingInformationLane public

pmtaTpmfLane : ManufacturingInformationLane
pmtaTpmfLane = manufacturing-information-lane
  "PMTA / Tobacco Product Master File / MRTPA supporting chemistry"
  true true true false

------------------------------------------------------------------------
-- EXACT CURRENT FRONTIER
------------------------------------------------------------------------

record AcquisitionFrontier : Set where
  constructor acquisition-frontier
  field
    sameDevicePuffResolvedAerosolPublicPaid : Bool
    sameDevicePuffResolvedTargetedDisposablePaid : Bool
    aerosolBroadNonTargetPublicPaid : Bool
    applicationNonTargetExistencePaid : Bool
    exactFourGatePublicReceiptPaid : Bool
    exactFourGatePrivateOrRedactedPossible : Bool
    notLocatedImpliesNotPerformed : Bool
    nextPublicTargets : String
    nextAccessTargets : String
open AcquisitionFrontier public

canonicalAcquisitionFrontier : AcquisitionFrontier
canonicalAcquisitionFrontier = acquisition-frontier
  true true true true false true false
  "2026 papers, CORESTA proceedings, university theses/dissertations, government-lab reports, supporting information and product-specific end-of-life studies"
  "public FDA TPL reviews and, where lawfully obtainable, applicant/TPMF/PMTA chemistry summaries or released supporting documents"

------------------------------------------------------------------------
-- WELD: WHAT THE PUBLIC LITERATURE ALREADY DEMONSTRATES SEPARATELY
------------------------------------------------------------------------

record ExperimentalWeld : Set where
  constructor experimental-weld
  field
    longitudinalCollectionPrimitive : String
    nonTargetPrimitive : String
    carbonylPrimitive : String
    elementalPrimitive : String
    materialsPrimitive : String
    missingWeld : String
open ExperimentalWeld public

canonicalExperimentalWeld : ExperimentalWeld
canonicalExperimentalWeld = experimental-weld
  "100-puff stage-indexed collection on the same disposable is already demonstrated"
  "GC/LC-HRMS non-target liquid/aerosol discovery is already demonstrated"
  "short-block dedicated carbonyl collection is already demonstrated"
  "puff-resolved ICP-MS aerosol metals are already demonstrated"
  "spent-device/component attribution is already demonstrated"
  "apply all modalities to the same stage ledger for the same physical disposable family and retain unresolved features across stages"

------------------------------------------------------------------------
-- HARD FIREWALLS
------------------------------------------------------------------------

data NotPubliclyLocatedMeansNeverPerformed : Set where
data PMTANonTargetMeansPublicRawData : Set where
data TargetedLifeCycleMeansNonTargetLifeCycle : Set where
data MethodFeasibilityCreatesExecutedWeld : Set where

notLocatedNotNeverPerformed : NotPubliclyLocatedMeansNeverPerformed → ⊥
notLocatedNotNeverPerformed ()

pmtaSummaryNotRawData : PMTANonTargetMeansPublicRawData → ⊥
pmtaSummaryNotRawData ()

targetedNotNonTarget : TargetedLifeCycleMeansNonTargetLifeCycle → ⊥
targetedNotNonTarget ()

feasibilityNotExecution : MethodFeasibilityCreatesExecutedWeld → ⊥
feasibilityNotExecution ()
