module DASHI.ComputerScience.CUDAROCmQuantumTernaryCrossPollinationExact where

open import DASHI.Core.Prelude
open import Data.Empty using (⊥)

import DASHI.ComputerScience.CUDAROCmExecutionBackendFibreExact as GPU
import DASHI.ComputerScience.QuantumExecutionFibreAdapterExact as Quantum
import DASHI.ComputerScience.BalancedTernaryQutritBasisBridgeExact as TritQutrit

------------------------------------------------------------------------
-- GPU / QUANTUM / TERNARY CROSS-POLLINATION
--
-- CUDA and ROCm are classical heterogeneous-compute backend fibres.  They may
-- execute a classical simulation of a quantum/qutrit object, but that does not
-- turn the GPU kernel into quantum execution.  Likewise the exact balanced
-- trit <-> qutrit basis labelling is not a physical qutrit realization.
------------------------------------------------------------------------

quantumExecutionBoundary : Quantum.QuantumExecutionFibreBoundary
quantumExecutionBoundary = Quantum.canonicalQuantumExecutionFibreBoundary

tritQutritBoundary : TritQutrit.BalancedTernaryQutritBasisBoundary
tritQutritBoundary = TritQutrit.canonicalBalancedTernaryQutritBasisBoundary

gpuBackendBoundary : GPU.CUDAROCmBackendBoundary
gpuBackendBoundary = GPU.canonicalCUDAROCmBackendBoundary

data ExecutionParadigm : Set where
  classicalCPUExecution : ExecutionParadigm
  classicalGPUExecution : ExecutionParadigm
  quantumCircuitExecution : ExecutionParadigm
  classicalQuantumSimulation : ExecutionParadigm

data RepresentationParadigm : Set where
  binaryRepresentation : RepresentationParadigm
  balancedTernaryRepresentation : RepresentationParadigm
  qutritBasisRepresentation : RepresentationParadigm
  generalQuantumStateRepresentation : RepresentationParadigm

record CrossParadigmReceipt : Set where
  constructor cross-paradigm-receipt
  field
    executionParadigm : ExecutionParadigm
    representationParadigm : RepresentationParadigm
    logicalIdentityReference : Bool
    physicalExecutionIdentityPaid : Bool
    performanceIdentityPaid : Bool
open CrossParadigmReceipt public

balancedTritOnCUDA : CrossParadigmReceipt
balancedTritOnCUDA =
  cross-paradigm-receipt
    classicalGPUExecution
    balancedTernaryRepresentation
    true false false

balancedTritOnROCm : CrossParadigmReceipt
balancedTritOnROCm =
  cross-paradigm-receipt
    classicalGPUExecution
    balancedTernaryRepresentation
    true false false

qutritBasisClassicallySimulatedOnGPU : CrossParadigmReceipt
qutritBasisClassicallySimulatedOnGPU =
  cross-paradigm-receipt
    classicalQuantumSimulation
    qutritBasisRepresentation
    true false false

------------------------------------------------------------------------
-- WrongType firewalls.
------------------------------------------------------------------------

data GPUQutritSimulationIsPhysicalQutrit : Set where
data BalancedTritEncodingIsQuantumSuperposition : Set where
data SameBasisLabelsMeanSameExecutionParadigm : Set where
data GPUAccelerationProvesQuantumSpeedup : Set where

gpuSimulationDoesNotBecomePhysicalQutrit : GPUQutritSimulationIsPhysicalQutrit → ⊥
gpuSimulationDoesNotBecomePhysicalQutrit ()

tritDoesNotBecomeSuperposition : BalancedTritEncodingIsQuantumSuperposition → ⊥
tritDoesNotBecomeSuperposition ()

basisLabelsDoNotIdentifyExecutionParadigm : SameBasisLabelsMeanSameExecutionParadigm → ⊥
basisLabelsDoNotIdentifyExecutionParadigm ()

gpuAccelerationDoesNotProveQuantumSpeedup : GPUAccelerationProvesQuantumSpeedup → ⊥
gpuAccelerationDoesNotProveQuantumSpeedup ()

record CUDAROCmQuantumTernaryBoundary : Set where
  constructor cuda-rocm-quantum-ternary-boundary
  field
    ternaryRepresentationMayUseGPUBackend : Bool
    qutritBasisMayBeClassicallyRepresented : Bool
    classicalGPUSimulationEqualsQuantumExecution : Bool
    basisEquivalenceEqualsPhysicalRealisation : Bool
    backendAccelerationEqualsQuantumAdvantage : Bool
open CUDAROCmQuantumTernaryBoundary public

canonicalCUDAROCmQuantumTernaryBoundary : CUDAROCmQuantumTernaryBoundary
canonicalCUDAROCmQuantumTernaryBoundary =
  cuda-rocm-quantum-ternary-boundary true true false false false
