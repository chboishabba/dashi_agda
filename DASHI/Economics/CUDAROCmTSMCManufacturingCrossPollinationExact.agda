module DASHI.Economics.CUDAROCmTSMCManufacturingCrossPollinationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Wikimedia.SnowballExternalIdentityAvailabilityExact as ExternalIdentity
import DASHI.ComputerScience.CUDAROCmExecutionBackendFibreExact as GPU
import DASHI.Economics.TSMCHBMManufacturingDemandPolicy2026Exact as TSMC

------------------------------------------------------------------------
-- CUDA / ROCm SOFTWARE BACKENDS <-> TSMC MANUFACTURING COORDINATE
--
-- Software/platform identity is not foundry identity.  The existing TSMC owner
-- supports foundry/advanced-packaging capacity and AI/HPC demand coordinates;
-- it does not identify the foundry for an arbitrary NVIDIA/AMD GPU, nor prove
-- supply, package, node, die, HBM stack, or commercial availability.
------------------------------------------------------------------------

tsmc2026PrimarySource : Attribution.AttributedSource
tsmc2026PrimarySource =
  Attribution.mkNoDOISource
    "Taiwan Semiconductor Manufacturing Company Limited"
    "2026 General Shareholders' Meeting Agenda / Business Report"
    "TSMC Investor Relations"
    "2026"
    "https://investor.tsmc.com/sites/ir/shareholders-meeting/2026-06-04/2026AGM_Agenda_wmn_0.pdf"
    Attribution.institutionalSource
    "primary manufacturing-demand source: TSMC reports leading-edge and advanced-packaging investment, customer/customer-customer capacity planning, and AI/HPC demand; not a device-specific CUDA/ROCm foundry receipt"
    Attribution.publicAttribution

tsmcQID : ExternalIdentity.ExternalIdentityDemand
tsmcQID =
  ExternalIdentity.mkOptionalIdentityDemand
    "GPU manufacturing attribution"
    "TSMC Taiwan Semiconductor Manufacturing Company"
    "TSMC"
    ExternalIdentity.wikidataQid
    (ExternalIdentity.verified "Wikidata" "Q713418")

record SoftwareManufacturingBridgeReceipt : Set where
  constructor software-manufacturing-bridge-receipt
  field
    softwareBackendReference : String
    vendorReference : String
    manufacturingReference : String
    sourceReference : String
    softwareIdentityKnown : Bool
    foundryIdentityForSpecificDeviceKnown : Bool
    exactProcessNodeKnown : Bool
    exactAdvancedPackagingKnown : Bool
    exactHBMAssemblyKnown : Bool
    supplyAvailabilityKnown : Bool
open SoftwareManufacturingBridgeReceipt public

cudaManufacturingBoundaryReceipt : SoftwareManufacturingBridgeReceipt
cudaManufacturingBoundaryReceipt =
  software-manufacturing-bridge-receipt
    "CUDA"
    "NVIDIA"
    "TSMC manufacturing-demand coordinate"
    "NVIDIA CUDA primary docs + TSMC 2026 primary materials"
    true false false false false false

rocmManufacturingBoundaryReceipt : SoftwareManufacturingBridgeReceipt
rocmManufacturingBoundaryReceipt =
  software-manufacturing-bridge-receipt
    "ROCm/HIP"
    "AMD"
    "TSMC manufacturing-demand coordinate"
    "AMD ROCm/HIP primary docs + TSMC 2026 primary materials"
    true false false false false false

existingTSMCCalibration : TSMC.ManufacturingDemandPolicyCalibration
existingTSMCCalibration = TSMC.canonicalManufacturingDemandPolicyCalibration

gpuBackendBoundary : GPU.CUDAROCmBackendBoundary
gpuBackendBoundary = GPU.canonicalCUDAROCmBackendBoundary

------------------------------------------------------------------------
-- WrongType firewalls.
------------------------------------------------------------------------

data CUDAImpliesTSMCFabricatedDevice : Set where
data ROCmImpliesTSMCFabricatedDevice : Set where
data TSMCAIDemandImpliesSpecificGPUAvailability : Set where
data AdvancedPackagingDemandIdentifiesExactPackage : Set where
data SoftwarePerformanceImpliesManufacturingPerformance : Set where

cudaDoesNotIdentifyFoundry : CUDAImpliesTSMCFabricatedDevice → ⊥
cudaDoesNotIdentifyFoundry ()

rocmDoesNotIdentifyFoundry : ROCmImpliesTSMCFabricatedDevice → ⊥
rocmDoesNotIdentifyFoundry ()

tsmcDemandDoesNotPaySpecificGPUAvailability : TSMCAIDemandImpliesSpecificGPUAvailability → ⊥
tsmcDemandDoesNotPaySpecificGPUAvailability ()

advancedPackagingDemandDoesNotIdentifyPackage : AdvancedPackagingDemandIdentifiesExactPackage → ⊥
advancedPackagingDemandDoesNotIdentifyPackage ()

softwarePerformanceDoesNotBecomeManufacturingPerformance : SoftwarePerformanceImpliesManufacturingPerformance → ⊥
softwarePerformanceDoesNotBecomeManufacturingPerformance ()

record CUDAROCmTSMCBoundary : Set where
  constructor cuda-rocm-tsmc-boundary
  field
    softwareAndFoundryAxesSeparated : Bool
    tsmcPrimaryDemandCoordinateRetained : Bool
    tsmcQIDRetained : Bool
    deviceSpecificFoundryReceiptPaid : Bool
    deviceSpecificNodeReceiptPaid : Bool
    deviceSpecificPackageReceiptPaid : Bool
    deviceSpecificSupplyReceiptPaid : Bool
open CUDAROCmTSMCBoundary public

canonicalCUDAROCmTSMCBoundary : CUDAROCmTSMCBoundary
canonicalCUDAROCmTSMCBoundary =
  cuda-rocm-tsmc-boundary true true true false false false false
