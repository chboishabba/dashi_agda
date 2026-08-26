module DASHI.Cognition.PNF.ExecutionEngineTournamentExact where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; suc)
open import Data.Empty using (⊥)

open import DASHI.Cognition.PNF.ComplexityArithmetic using (_≤ᶜ_)

------------------------------------------------------------------------
-- Engine selection is workload-relative and authority-preserving.
--
-- PostgreSQL, packed/native code, NumPy-like array execution, custom sparse
-- worklists, Zelph, and generic Datalog are implementation candidates.  No
-- engine receives architectural privilege by name.  It must preserve the same
-- authority and produce a measured work advantage for the kernel geometry it
-- claims to own.
------------------------------------------------------------------------

data Engine : Set where
  postgresqlEngine
  packedNativeEngine
  numpyArrayEngine
  customWorklistEngine
  zelphEngine
  datalogEngine : Engine

data KernelGeometry : Set where
  localBoundedFibre
  globalIndexedExposure
  sparseDeltaClosure : KernelGeometry

record EngineRun (Input Output : Set) : Set₁ where
  constructor engineRun
  field
    engine : Engine
    geometry : KernelGeometry
    run : Input → Output
    wallWork : Input → Nat
    cpuWork : Input → Nat
    bytesRead : Input → Nat
    bytesWritten : Input → Nat
    boundaryCrossings : Input → Nat

open EngineRun public

record AuthorityEquivalent
    {Input Output : Set}
    (reference candidate : EngineRun Input Output) : Set where
  constructor authorityEquivalent
  field
    sameOutput :
      (input : Input) →
      run candidate input ≡ run reference input

open AuthorityEquivalent public

record CandidateEarnsKeep
    {Input Output : Set}
    (reference candidate : EngineRun Input Output) : Set where
  constructor candidateEarnsKeep
  field
    authorityExact : AuthorityEquivalent reference candidate
    wallNoWorse :
      (input : Input) → wallWork candidate input ≤ᶜ wallWork reference input
    cpuNoWorse :
      (input : Input) → cpuWork candidate input ≤ᶜ cpuWork reference input
    boundaryNoWorse :
      (input : Input) →
      boundaryCrossings candidate input ≤ᶜ boundaryCrossings reference input

open CandidateEarnsKeep public

------------------------------------------------------------------------
-- A stronger promotion certificate additionally requires a strict wall-work win
-- on at least one representative workload.  The witness is encoded as
-- suc(candidate) <= reference rather than importing a second arithmetic order.
------------------------------------------------------------------------

record EnginePromotion
    {Input Output : Set}
    (reference candidate : EngineRun Input Output) : Set₁ where
  constructor enginePromotion
  field
    earnsKeep : CandidateEarnsKeep reference candidate
    witnessInput : Input
    strictWallWin :
      suc (wallWork candidate witnessInput)
        ≤ᶜ wallWork reference witnessInput

open EnginePromotion public

------------------------------------------------------------------------
-- Geometry is a benchmark partition, not a preselected implementation.
------------------------------------------------------------------------

data ZelphArchitecturalPrivilege : Set where

data PostgreSQLArchitecturalPrivilege : Set where

data NumPyArchitecturalPrivilege : Set where

data NativeArchitecturalPrivilege : Set where

zelphMustEarnItsKeep : ZelphArchitecturalPrivilege → ⊥
zelphMustEarnItsKeep ()

postgresqlMustEarnItsKeep : PostgreSQLArchitecturalPrivilege → ⊥
postgresqlMustEarnItsKeep ()

numpyMustEarnItsKeep : NumPyArchitecturalPrivilege → ⊥
numpyMustEarnItsKeep ()

nativeMustEarnItsKeep : NativeArchitecturalPrivilege → ⊥
nativeMustEarnItsKeep ()

------------------------------------------------------------------------
-- The intended tournament partitions the dream flow into the three distinct
-- computational geometries discussed in the runtime design.
------------------------------------------------------------------------

canonicalLocalGeometry : KernelGeometry
canonicalLocalGeometry = localBoundedFibre

canonicalGlobalExposureGeometry : KernelGeometry
canonicalGlobalExposureGeometry = globalIndexedExposure

canonicalSparseClosureGeometry : KernelGeometry
canonicalSparseClosureGeometry = sparseDeltaClosure
