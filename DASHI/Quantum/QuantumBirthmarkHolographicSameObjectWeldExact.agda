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
-- The upstream module defines
--   treeEntanglementEntropy k = k * log 2
-- and proves the corresponding minimal-cut area-law identity by rfl. It also
-- defines holographicContract, a uniform diagonal boundary density matrix.
--
-- The native dashi_lean4 producer now closes two mathematical gaps:
--   * full contract: S(rho_n) = n log 2;
--   * explicit factorisation 2^(k+r)=2^k*2^r: the diagonal partial trace has
--     eigenvalue 2^(-k), hence reduced entropy k log 2.
--
-- Consequently the remaining RT seam is not the entropy algebra. It is the
-- same-object carrier identification between upstream's `ZMod (2^n)` depth-k
-- subtree and the explicit tensor-product/partial-trace factorisation used by
-- the Lean producer. Upstream itself does not define that map.
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
    factorizedSubsystemEntropyWeldClosed : Bool

    upstreamZModSubsystemFactorizationStillRequired : Bool
    subsystemReducedDensityMatrixWeldStillRequired : Bool
    upstreamSubsystemPartialTraceDefined : Bool

    areaLawDoesNotByItselfComputeUpstreamSubsystemVonNeumannEntropy : Bool

canonicalHolographicTensorNetworkClaimBoundary :
  HolographicTensorNetworkClaimBoundary
canonicalHolographicTensorNetworkClaimBoundary =
  holographicTensorNetworkClaimBoundary
    true true true true
    true true
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
-- Remaining same-object obligation: upstream subtree / tensor factorisation.
------------------------------------------------------------------------

record UpstreamSubsystemFactorisationObligation : Set₁ where
  field
    UpstreamBoundaryCarrier : Set
    FactorizedBoundaryCarrier : Set
    ReducedDensityMatrix : Set

    upstreamBoundaryCarrier : UpstreamBoundaryCarrier
    factorizedBoundaryCarrier : FactorizedBoundaryCarrier
    reducedDensityMatrix : ReducedDensityMatrix

    zModToTensorProductFactorisation : Set
    zModToTensorProductFactorisationProof : zModToTensorProductFactorisation

    depthKSubtreeMatchesSelectedFactor : Set
    depthKSubtreeMatchesSelectedFactorProof : depthKSubtreeMatchesSelectedFactor

    upstreamPartialTraceMatchesFactorizedMarginal : Set
    upstreamPartialTraceMatchesFactorizedMarginalProof :
      upstreamPartialTraceMatchesFactorizedMarginal

record SameObjectPromotionFirewall : Set where
  constructor sameObjectPromotionFirewall
  field
    fullStateEntropyIsNotAutomaticallySubsystemEntropy : Bool
    factorizedSubsystemEntropyIsNotAutomaticallyUpstreamSubtreeEntropy : Bool
    reflexiveAreaLawIsNotCarrierIdentification : Bool
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

factorizedSubsystemEntropyWeldClosed : Bool
factorizedSubsystemEntropyWeldClosed =
  ContractEntropy.factorizedSubsystemRTClosed

upstreamZModSubsystemFactorizationStillRequired : Bool
upstreamZModSubsystemFactorizationStillRequired =
  ContractEntropy.upstreamZModSubsystemFactorizationStillRequired

subsystemReducedDensityMatrixWeldStillRequired : Bool
subsystemReducedDensityMatrixWeldStillRequired =
  upstreamZModSubsystemFactorizationStillRequired

ryuTakayanagiAreaLawShapeOwned : Bool
ryuTakayanagiAreaLawShapeOwned = true

areaLawDoesNotComputeVonNeumannEntropyOfContract : Bool
areaLawDoesNotComputeVonNeumannEntropyOfContract = true

densityMatrixEntropyWeldRequired : Bool
densityMatrixEntropyWeldRequired = subsystemReducedDensityMatrixWeldStillRequired
