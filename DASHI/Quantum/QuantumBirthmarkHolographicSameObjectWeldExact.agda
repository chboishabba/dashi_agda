{-# OPTIONS --safe #-}
module DASHI.Quantum.QuantumBirthmarkHolographicSameObjectWeldExact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.String using (String)

import DASHI.Quantum.QuantumBirthmarkHolographicContractEntropyExact as ContractEntropy
import DASHI.Quantum.QuantumBirthmarkCorrectedRTSameObjectExact as CorrectedRT

------------------------------------------------------------------------
-- SAME-OBJECT HOLOGRAPHIC ENTROPY WELD
--
-- Upstream inspected source:
--   sneed-and-feed/adelic-spectral-zeta
--   formalization/Formalization/Quantum/HolographicTensorNetwork.lean
--
-- The entropy algebra is no longer the RT residual. Native dashi_lean4
-- producers establish:
--
--   * the inspected uniform diagonal contract has S(rho_n) = n log 2;
--   * an explicit product marginal has entropy k log 2;
--   * a corrected maximally-entangled Schmidt density kernel, on one actual
--     joint carrier, reduces by partial trace to the same uniform marginal and
--     therefore satisfies S(rho_A) = k log 2 = corrected cut entropy.
--
-- What remains is source/carrier identity: the inspected upstream named state,
-- its ZMod subtree and its geometric cut have not been identified with that
-- corrected tensor-product state.  That is a different theorem from entropy.
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
    correctedFiniteRTEntropyWeldClosed : Bool

    subsystemReducedDensityMatrixWeldStillRequired : Bool
    upstreamStateCarrierWeldStillRequired : Bool
    upstreamZModSubsystemFactorizationStillRequired : Bool
    upstreamSubsystemPartialTraceDefined : Bool

    areaLawDoesNotByItselfIdentifyUpstreamStateWithCorrectedState : Bool

canonicalHolographicTensorNetworkClaimBoundary :
  HolographicTensorNetworkClaimBoundary
canonicalHolographicTensorNetworkClaimBoundary =
  holographicTensorNetworkClaimBoundary
    true true true true
    true true true
    false true true false
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
-- Remaining source/carrier obligation.
------------------------------------------------------------------------

record UpstreamCorrectedRTIdentificationObligation : Set₁ where
  field
    UpstreamBoundaryState : Set
    CorrectedEntangledState : Set
    GeometricCutCarrier : Set
    SelectedTensorFactor : Set

    upstreamBoundaryState : UpstreamBoundaryState
    correctedEntangledState : CorrectedEntangledState
    geometricCutCarrier : GeometricCutCarrier
    selectedTensorFactor : SelectedTensorFactor

    upstreamStateEqualsCorrectedState : Set
    upstreamStateEqualsCorrectedStateProof : upstreamStateEqualsCorrectedState

    zModToTensorProductFactorisation : Set
    zModToTensorProductFactorisationProof : zModToTensorProductFactorisation

    depthKSubtreeMatchesSelectedFactor : Set
    depthKSubtreeMatchesSelectedFactorProof : depthKSubtreeMatchesSelectedFactor

    geometricMinimalCutMatchesSelectedFactor : Set
    geometricMinimalCutMatchesSelectedFactorProof :
      geometricMinimalCutMatchesSelectedFactor

record SameObjectPromotionFirewall : Set where
  constructor sameObjectPromotionFirewall
  field
    entropyEqualityDoesNotIdentifyStates : Bool
    factorizedSubsystemEntropyIsNotAutomaticallyUpstreamSubtreeEntropy : Bool
    correctedFiniteRTIsNotAutomaticallyUpstreamRT : Bool
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

correctedFiniteRTEntropyWeldClosed : Bool
correctedFiniteRTEntropyWeldClosed =
  CorrectedRT.correctedRTSameObjectEntropy

subsystemReducedDensityMatrixWeldStillRequired : Bool
subsystemReducedDensityMatrixWeldStillRequired = false

upstreamStateCarrierWeldStillRequired : Bool
upstreamStateCarrierWeldStillRequired = true

upstreamZModSubsystemFactorizationStillRequired : Bool
upstreamZModSubsystemFactorizationStillRequired = true

ryuTakayanagiAreaLawShapeOwned : Bool
ryuTakayanagiAreaLawShapeOwned = true

areaLawDoesNotComputeVonNeumannEntropyOfContract : Bool
areaLawDoesNotComputeVonNeumannEntropyOfContract = true

-- Legacy name retained for consumers. The corrected finite density-matrix
-- entropy weld is closed; the live obligation is source/carrier identity.
densityMatrixEntropyWeldRequired : Bool
densityMatrixEntropyWeldRequired = false
