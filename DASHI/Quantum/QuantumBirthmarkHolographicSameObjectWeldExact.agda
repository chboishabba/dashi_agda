{-# OPTIONS --safe #-}
module DASHI.Quantum.QuantumBirthmarkHolographicSameObjectWeldExact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.String using (String)

import DASHI.Quantum.QuantumBirthmarkHolographicContractEntropyExact as ContractEntropy

------------------------------------------------------------------------
-- SAME-OBJECT HOLOGRAPHIC ENTROPY WELD
--
-- Upstream inspected source:
--   sneed-and-feed/adelic-spectral-zeta
--   formalization/Formalization/Quantum/HolographicTensorNetwork.lean
--
-- The upstream module genuinely defines
--   treeEntanglementEntropy k = k * log 2
-- and proves the corresponding minimal-cut area-law identity by rfl.
-- It also defines holographicContract, a boundary density matrix.
--
-- The full-state gap is now sharpened/partly closed by
-- `QuantumBirthmarkHolographicContractEntropyExact`: the inspected contract is
-- uniform diagonal of dimension 2^n with eigenvalue 2^(-n), and the native
-- dashi_lean4 producer proves the corresponding spectral entropy n log 2.
-- Therefore the full-depth same-object weld is available from that producer.
--
-- What remains is the genuinely stronger RT subsystem theorem: upstream does
-- not define the reduced density matrix / partial trace for a depth-k subsystem
-- of a depth-n network.  We therefore keep that subsystem weld explicit and do
-- not promote the full-state theorem into the k <= n claim.
------------------------------------------------------------------------

upstreamRepository : String
upstreamRepository = "sneed-and-feed/adelic-spectral-zeta"

upstreamSourcePath : String
upstreamSourcePath =
  "formalization/Formalization/Quantum/HolographicTensorNetwork.lean"

upstreamCutEntropyDefinition : String
upstreamCutEntropyDefinition = "treeEntanglementEntropy"

upstreamBoundaryDensityMatrixDefinition : String
upstreamBoundaryDensityMatrixDefinition = "holographicContract"

record HolographicTensorNetworkClaimBoundary : Set where
  constructor holographicTensorNetworkClaimBoundary
  field
    treeEntanglementEntropyDefined : Bool
    holographicContractDefined : Bool
    ryuTakayanagiAreaLawShapeOwned : Bool
    discreteExistentialEntropyTheoremOwned : Bool

    fullStateDensityMatrixEntropyWeldClosed : Bool
    subsystemReducedDensityMatrixWeldStillRequired : Bool
    upstreamSubsystemPartialTraceDefined : Bool

    areaLawDoesNotByItselfComputeSubsystemVonNeumannEntropy : Bool

canonicalHolographicTensorNetworkClaimBoundary :
  HolographicTensorNetworkClaimBoundary
canonicalHolographicTensorNetworkClaimBoundary =
  holographicTensorNetworkClaimBoundary
    true true true true
    true true false
    true

------------------------------------------------------------------------
-- Generic same-object compiler.
------------------------------------------------------------------------

record BoundaryEntropySameObjectData : Set₁ where
  field
    BoundaryState : Set
    EntropyValue : Set

    constructedBoundaryState : BoundaryState
    entropyOf : BoundaryState → EntropyValue
    cutEntropy : EntropyValue

    sameObjectEntropyWeld :
      entropyOf constructedBoundaryState ≡ cutEntropy

open BoundaryEntropySameObjectData public

sameObjectBoundaryEntropyCompiler :
  (D : BoundaryEntropySameObjectData) →
  entropyOf D (constructedBoundaryState D) ≡ cutEntropy D
sameObjectBoundaryEntropyCompiler D = sameObjectEntropyWeld D

------------------------------------------------------------------------
-- Remaining analytic obligation: subsystem reduced state.
------------------------------------------------------------------------

record SubsystemDensityMatrixEntropyObligation : Set₁ where
  field
    FullDensityMatrix : Set
    ReducedDensityMatrix : Set
    EntropyValue : Set

    holographicContract : FullDensityMatrix
    reducedDensityMatrix : ReducedDensityMatrix
    treeEntanglementEntropy : EntropyValue
    vonNeumannEntropy : ReducedDensityMatrix → EntropyValue

    partialTraceFromFullContract : Set
    partialTraceFromFullContractProof : partialTraceFromFullContract

    reducedContractEntropyEqualsTreeEntropy : Set
    reducedContractEntropyEqualsTreeEntropyProof :
      reducedContractEntropyEqualsTreeEntropy

record SameObjectPromotionFirewall : Set where
  constructor sameObjectPromotionFirewall
  field
    fullStateEntropyIsNotAutomaticallySubsystemEntropy : Bool
    reflexiveAreaLawIsNotSubsystemDensityMatrixSpectralCalculation : Bool
    existentialEntropyWitnessDoesNotConstructReducedDensityMatrix : Bool
    tensorNetworkAreaLawDoesNotByItselfEstablishPhysicalAdSCFT : Bool
    birthmarkMemoryIsNotBoundaryEntanglementEntropyByDefinition : Bool

canonicalSameObjectPromotionFirewall : SameObjectPromotionFirewall
canonicalSameObjectPromotionFirewall =
  sameObjectPromotionFirewall true true true true true

------------------------------------------------------------------------
-- Compact status.
------------------------------------------------------------------------

fullStateDensityMatrixEntropyWeldClosed : Bool
fullStateDensityMatrixEntropyWeldClosed =
  ContractEntropy.fullStateEntropyMatchesTreeEntropyAtFullDepth

subsystemReducedDensityMatrixWeldStillRequired : Bool
subsystemReducedDensityMatrixWeldStillRequired = true

ryuTakayanagiAreaLawShapeOwned : Bool
ryuTakayanagiAreaLawShapeOwned = true

areaLawDoesNotComputeVonNeumannEntropyOfContract : Bool
areaLawDoesNotComputeVonNeumannEntropyOfContract = true

densityMatrixEntropyWeldRequired : Bool
densityMatrixEntropyWeldRequired = subsystemReducedDensityMatrixWeldStillRequired
