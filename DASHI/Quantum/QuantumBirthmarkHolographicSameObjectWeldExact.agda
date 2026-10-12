{-# OPTIONS --safe #-}
module DASHI.Quantum.QuantumBirthmarkHolographicSameObjectWeldExact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.String using (String)

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
-- What it does NOT prove is that a von-Neumann entropy computed from that
-- holographicContract is treeEntanglementEntropy k.  This owner names exactly
-- that same-object residual and provides a typed compiler once such a proof is
-- supplied.  It does not manufacture the missing spectral/logarithmic proof.
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
    densityMatrixEntropyWeldRequired : Bool
    vonNeumannEntropyOfContractProvedUpstream : Bool
    areaLawDoesNotComputeVonNeumannEntropyOfContract : Bool

canonicalHolographicTensorNetworkClaimBoundary :
  HolographicTensorNetworkClaimBoundary
canonicalHolographicTensorNetworkClaimBoundary =
  holographicTensorNetworkClaimBoundary
    true true true true true false true

------------------------------------------------------------------------
-- Generic same-object compiler.
--
-- This closes the logical transport once a consumer supplies the actual
-- entropy evaluator and proves that it evaluates the constructed boundary
-- state to the cut entropy owned by the area-law lane.
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
-- Remaining analytic obligation for the inspected tensor-network source.
------------------------------------------------------------------------

record DensityMatrixEntropyObligation : Set₁ where
  field
    DensityMatrix : Set
    EntropyValue : Set
    holographicContract : DensityMatrix
    treeEntanglementEntropy : EntropyValue
    vonNeumannEntropy : DensityMatrix → EntropyValue

    densityMatrixEntropyWeld : Set
    densityMatrixEntropyWeldProof : densityMatrixEntropyWeld

    contractEntropyEqualsTreeEntropy : Set
    contractEntropyEqualsTreeEntropyProof : contractEntropyEqualsTreeEntropy

record SameObjectPromotionFirewall : Set where
  constructor sameObjectPromotionFirewall
  field
    namedEntropyIsNotAutomaticallyEntropyOfNamedDensityMatrix : Bool
    reflexiveAreaLawIsNotDensityMatrixSpectralCalculation : Bool
    existentialEntropyWitnessDoesNotCloseSameObjectWeld : Bool
    tensorNetworkAreaLawDoesNotByItselfEstablishPhysicalAdSCFT : Bool
    birthmarkMemoryIsNotBoundaryEntanglementEntropyByDefinition : Bool

canonicalSameObjectPromotionFirewall : SameObjectPromotionFirewall
canonicalSameObjectPromotionFirewall =
  sameObjectPromotionFirewall true true true true true

densityMatrixEntropyWeldRequired : Bool
densityMatrixEntropyWeldRequired = true

ryuTakayanagiAreaLawShapeOwned : Bool
ryuTakayanagiAreaLawShapeOwned = true

areaLawDoesNotComputeVonNeumannEntropyOfContract : Bool
areaLawDoesNotComputeVonNeumannEntropyOfContract = true
