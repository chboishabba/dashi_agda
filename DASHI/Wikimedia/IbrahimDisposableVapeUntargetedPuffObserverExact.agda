module DASHI.Wikimedia.IbrahimDisposableVapeUntargetedPuffObserverExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Wikimedia.IbrahimDisposableVapeSameDeviceLongitudinalCensusExact as Longitudinal
import DASHI.Wikimedia.IbrahimDisposableVapePublicPrivateAcquisitionFrontierExact as Frontier

------------------------------------------------------------------------
-- UNTARGED PUFF-RESOLVED ORGANIC OBSERVER ACQUISITION
--
-- This tranche sharpens the previously unpaid four-gate receipt.  Gao et al.
-- pay puff-resolved + direct aerosol + broad untargeted organic chemistry in
-- one experiment.  The remaining unpaid coordinate is deployment across the
-- observed whole life of a modern disposable.
------------------------------------------------------------------------

record FourGateReceipt : Set where
  constructor four-gate-receipt
  field
    sourceLabel : String
    doiOrReference : String
    samePhysicalDevice : Bool
    puffResolved : Bool
    aerosolObserved : Bool
    broadOrganicUntargeted : Bool
    wholeLifeDisposable : Bool
    rawDataPublicOrRequestable : String
    supportedClaim : String
    excludedPromotion : String
open FourGateReceipt public

gaoPuffUntargeted : FourGateReceipt
gaoPuffUntargeted = four-gate-receipt
  "Gao et al. Rapid Untargeted Puff-by-Puff Analysis of (Electronic) Cigarette Emissions by DBDI-FT-MS"
  "10.1002/anse.202400079"
  true true true true false
  "raw high-resolution MS data reported available from the authors upon reasonable request"
  "five ECs from two brands were analysed directly; four puffs per EC were resolved in a five-minute acquisition; 225 compounds were uncovered across broad chemical classes"
  "short proof-of-concept runs do not establish a whole-life modern-disposable trajectory"

chimia2026Followup : FourGateReceipt
chimia2026Followup = four-gate-receipt
  "Gao et al. Vaping with a Mass Spectrometer — On the Road to Profile all Chemicals in E-Cigarette Puffs in Minutes"
  "10.2533/chimia.2026.178"
  true true true true false
  "open-access analytical highlight; derivative/follow-up account of the DBDI puff-resolved method"
  "confirms the analytical programme and reproducible direct-puff untargeted workflow"
  "not independent evidence of whole-life disposable sampling"

record StandardsReceipt : Set where
  constructor standards-receipt
  field
    body : String
    document : String
    publicationDate : String
    scope : String
    paid : Bool
open StandardsReceipt public

corestaGuide39 : StandardsReceipt
corestaGuide39 = standards-receipt
  "CORESTA EVAP + HTP Sub-Groups"
  "Guide No. 39 — Technical Guide for Non-Targeted Analysis of Electronic Cigarette and Heated Tobacco Emissions"
  "2026-08"
  "best-practice surface for non-targeted emissions analysis; joint e-vapour / heated-tobacco scope"
  true

------------------------------------------------------------------------
-- ACQUISITION MATRIX
------------------------------------------------------------------------

record GateMatrix : Set where
  constructor gate-matrix
  field
    puffResolvedUntargetedPublicPaid : Bool
    directAerosolUntargetedPublicPaid : Bool
    broadOrganicClassesPublicPaid : Bool
    modernDisposableWholeLifeUntargetedPublicPaid : Bool
    sameDeviceWholeLifeMetalsPaid : Bool
    sameDeviceWholeLifeTargetedChemistryPaid : Bool
    nonTargetStandardsSurfacePaid : Bool
    exactWeldStillUnpaid : Bool
open GateMatrix public

canonicalGateMatrix : GateMatrix
canonicalGateMatrix = gate-matrix
  true true true false true true true true

------------------------------------------------------------------------
-- RESIDUAL REPAIR
------------------------------------------------------------------------

record ResidualRepair : Set where
  constructor residual-repair
  field
    oldResidual : String
    newResidual : String
    reason : String
    exactClosingExperiment : String
open ResidualRepair public

canonicalResidualRepair : ResidualRepair
canonicalResidualRepair = residual-repair
  "puff-resolved broad organic non-target aerosol chemistry not yet paid"
  "whole-life deployment of a puff-resolved broad organic non-target observer on one modern disposable remains unpaid"
  "Gao/Pavlou pay the analytical observer itself; existing disposable studies pay longitudinal stage collection, metals and targeted chemistry separately"
  "apply direct puff-resolved DBDI-FT-MS and/or stage-matched GC/LC-HRMS at predeclared early/mid/late points on the same physical disposable, synchronized with carbonyl/metals/material lanes"

------------------------------------------------------------------------
-- HARD FIREWALLS
------------------------------------------------------------------------

data ShortPuffRunCreatesWholeLifeTrajectory : Set where
data FiveDevicesCreateMarketDistribution : Set where
data UntargetedAssignmentCreatesQuantitativeExposure : Set where
data CorestaGuideCreatesEmpiricalResult : Set where
data RequestableRawDataCreatesAcquiredRawData : Set where

shortRunNotWholeLife : ShortPuffRunCreatesWholeLifeTrajectory → ⊥
shortRunNotWholeLife ()

fiveDevicesNotMarket : FiveDevicesCreateMarketDistribution → ⊥
fiveDevicesNotMarket ()

untargetedNotQuantitativeExposure : UntargetedAssignmentCreatesQuantitativeExposure → ⊥
untargetedNotQuantitativeExposure ()

guideNotEmpiricalResult : CorestaGuideCreatesEmpiricalResult → ⊥
guideNotEmpiricalResult ()

requestableNotAcquired : RequestableRawDataCreatesAcquiredRawData → ⊥
requestableNotAcquired ()

record UntargetedPuffBoundary : Set where
  constructor untargeted-puff-boundary
  field
    observerPrimitivePaid : Bool
    longitudinalDisposablePrimitivePaid : Bool
    standardsGuidancePaid : Bool
    rawMSDataAcquired : Bool
    exactPublicFourGateReceiptPaid : Bool
    exactExperimentSpecified : Bool
open UntargetedPuffBoundary public

canonicalUntargetedPuffBoundary : UntargetedPuffBoundary
canonicalUntargetedPuffBoundary = untargeted-puff-boundary
  true true true false false true
