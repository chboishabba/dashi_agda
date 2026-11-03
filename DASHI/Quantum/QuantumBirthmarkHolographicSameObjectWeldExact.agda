{-# OPTIONS --safe #-}
module DASHI.Quantum.QuantumBirthmarkHolographicSameObjectWeldExact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.String using (String)

import DASHI.Quantum.QuantumBirthmarkHolographicContractEntropyExact as ContractEntropy
import DASHI.Quantum.QuantumBirthmarkCorrectedRTSameObjectExact as CorrectedRT
import DASHI.Quantum.QuantumBirthmarkHolographicZModCarrierFactorizationBoundaryExact as CarrierFactor
import DASHI.Quantum.QuantumBirthmarkHolographicTensorNetworkAuditExact as Audit

------------------------------------------------------------------------
-- SAME-OBJECT HOLOGRAPHIC ENTROPY / STATE WELD
--
-- The finite entropy algebra and finite carrier algebra are no longer the live
-- RT obstruction.  Native dashi_lean4 producers now establish:
--
--   * the inspected uniform diagonal contract has S(rho_n) = n log 2;
--   * explicit reduced states with entropy k log 2;
--   * a corrected coherent Schmidt state with same-object partial trace;
--   * exact ZMod(2^(k+r)) <-> Fin(2^k) x Fin(2^r) carrier factorisation;
--   * corrected coherent states pulled back to the upstream ZMod carrier;
--   * for r >= k, a larger complement still gives the uniform 2^-k reduced
--     state and entropy k log 2.
--
-- Direct source inspection and a native Lean depth-one no-go also establish
-- something stronger than an unproved identity: the CURRENT upstream
-- `holographicState` and `holographicContract` are different objects.  The
-- former is a uniform pure state with nonzero off-diagonal coherence; the
-- latter is diagonal maximally mixed.  Therefore no proof of equality between
-- those current definitions should remain on the roadmap.
--
-- The live RT source task is replacement/equivalence:
--
--   actual corrected tree/tensor contraction
--       -> coherent corrected ZMod state
--       -> selected depth-k factor/subtree
--       -> geometric minimal cut
--       -> same reduced entropy already proved k log 2.
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

    -- Retained legacy names for downstream compatibility.  Their values now
    -- reflect the stronger current state.
    subsystemReducedDensityMatrixWeldStillRequired : Bool
    upstreamStateCarrierWeldStillRequired : Bool
    upstreamZModSubsystemFactorizationStillRequired : Bool
    upstreamSubsystemPartialTraceDefined : Bool

    correctedZModCarrierStateAvailable : Bool
    upstreamCurrentStateContractWeldImpossibleAsWritten : Bool
    upstreamDefinitionReplacementRequired : Bool
    geometricSubtreeAndMinimalCutWeldStillRequired : Bool

    areaLawDoesNotByItselfIdentifyUpstreamStateWithCorrectedState : Bool

canonicalHolographicTensorNetworkClaimBoundary :
  HolographicTensorNetworkClaimBoundary
canonicalHolographicTensorNetworkClaimBoundary =
  holographicTensorNetworkClaimBoundary
    true true true true
    true true true
    false true false false
    true true true true
    true

------------------------------------------------------------------------
-- Generic same-object entropy compiler.
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
-- Corrected upstream replacement obligation.
--
-- This is the proper successor to the older identity obligation.  The carrier
-- factorisation itself is already source-paid and therefore does not appear as
-- a new proof debt here.
------------------------------------------------------------------------

record CorrectedUpstreamRTReplacementObligation : Set₁ where
  field
    UpstreamTreeNetwork : Set
    CorrectedBoundaryState : Set
    GeometricDepthKSubtree : Set
    SelectedTensorFactor : Set
    GeometricMinimalCut : Set

    upstreamTreeNetwork : UpstreamTreeNetwork
    correctedBoundaryState : CorrectedBoundaryState
    geometricDepthKSubtree : GeometricDepthKSubtree
    selectedTensorFactor : SelectedTensorFactor
    geometricMinimalCut : GeometricMinimalCut

    treeContractionProducesCorrectedState : Set
    treeContractionProducesCorrectedStateProof :
      treeContractionProducesCorrectedState

    depthKSubtreeMatchesSelectedFactor : Set
    depthKSubtreeMatchesSelectedFactorProof :
      depthKSubtreeMatchesSelectedFactor

    geometricMinimalCutMatchesSelectedFactor : Set
    geometricMinimalCutMatchesSelectedFactorProof :
      geometricMinimalCutMatchesSelectedFactor

-- Legacy obligation retained only so older imports do not disappear.  Its
-- carrier-factorisation field should now be instantiated by the already-paid
-- native theorem rather than treated as a live research target.  Equality with
-- the CURRENT upstream named state must NOT be inhabited: the audit/no-go says
-- those definitions are incompatible.
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
    carrierEquivalenceDoesNotRepairStateDefinitionMismatch : Bool

canonicalSameObjectPromotionFirewall : SameObjectPromotionFirewall
canonicalSameObjectPromotionFirewall =
  sameObjectPromotionFirewall true true true true true true

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

-- Legacy broad name: true only because the actual upstream tree contraction
-- still has to be replaced/proved equivalent to the corrected state and welded
-- to the geometric cut.  It no longer denotes missing carrier cardinality.
upstreamStateCarrierWeldStillRequired : Bool
upstreamStateCarrierWeldStillRequired = true

upstreamZModSubsystemFactorizationStillRequired : Bool
upstreamZModSubsystemFactorizationStillRequired = false

correctedZModCarrierStateAvailable : Bool
correctedZModCarrierStateAvailable =
  CorrectedRT.correctedEntangledStateOnUpstreamCarrierSourceWritten

upstreamCurrentStateContractWeldImpossibleAsWritten : Bool
upstreamCurrentStateContractWeldImpossibleAsWritten =
  Audit.upstreamStateContractSameObjectImpossibleAsWritten

upstreamDefinitionReplacementRequired : Bool
upstreamDefinitionReplacementRequired =
  Audit.upstreamDefinitionReplacementRequired

geometricSubtreeAndMinimalCutWeldStillRequired : Bool
geometricSubtreeAndMinimalCutWeldStillRequired = true

ryuTakayanagiAreaLawShapeOwned : Bool
ryuTakayanagiAreaLawShapeOwned = true

areaLawDoesNotComputeVonNeumannEntropyOfContract : Bool
areaLawDoesNotComputeVonNeumannEntropyOfContract = true

-- Legacy name retained for consumers. The corrected finite density-matrix
-- entropy weld is closed; the live obligation is source replacement/equivalence
-- plus geometric subtree/minimal-cut semantics.
densityMatrixEntropyWeldRequired : Bool
densityMatrixEntropyWeldRequired = false
