{-# OPTIONS --safe #-}
module DASHI.Quantum.QuantumBirthmarkHolographicContractEntropyExact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- CONCRETE HOLOGRAPHIC CONTRACT ENTROPY RECEIPT
--
-- Source inspection of
--   sneed-and-feed/adelic-spectral-zeta/
--   formalization/Formalization/Quantum/HolographicTensorNetwork.lean
-- shows that `holographicContract n` is diagonal with dimension 2^n and
-- constant diagonal entry 2^(-n). Hence its spectrum is uniform with
-- multiplicity 2^n and its full-state von-Neumann entropy is n log 2.
--
-- The native Mathlib producer in
--   dashi_lean4/Synthesis/HolographicContractEntropy.lean (PR #68)
-- proves both:
--   * full-state entropy n log 2; and
--   * for an explicit factorisation 2^(k+r)=2^k*2^r, the diagonal partial
--     trace has eigenvalue 2^(-k) and entropy k log 2.
--
-- The remaining same-object RT seam is therefore only the identification of
-- upstream's `ZMod (2^n)` depth-k subtree with that explicit tensor-product
-- factorisation / reduced state. Upstream itself supplies no such partial-trace
-- construction, so that final identification stays fail-closed here.
------------------------------------------------------------------------

upstreamRepository : String
upstreamRepository = "sneed-and-feed/adelic-spectral-zeta"

upstreamSourcePath : String
upstreamSourcePath =
  "formalization/Formalization/Quantum/HolographicTensorNetwork.lean"

leanProducerRepository : String
leanProducerRepository = "chboishabba/dashi_lean4"

leanProducerPath : String
leanProducerPath = "Synthesis/HolographicContractEntropy.lean"

leanProducerPR : String
leanProducerPR = "https://github.com/chboishabba/dashi_lean4/pull/68"

record HolographicContractSpectrumReceipt : Set where
  constructor holographicContractSpectrumReceipt
  field
    holographicContractDefinedUpstream : Bool
    holographicContractIsUniformDiagonal : Bool
    dimensionIsTwoToDepth : Bool
    repeatedEigenvalueIsInverseTwoToDepth : Bool
    uniformEigenvalueMultiplicity : Bool
    uniformTraceNormalisation : Bool
    fullContractVonNeumannEntropyIsNLogTwo : Bool
    fullStateEntropyMatchesTreeEntropyAtFullDepth : Bool
    factorizedMarginalEigenvalueIsInverseTwoToK : Bool
    factorizedSubsystemRTClosed : Bool

canonicalHolographicContractSpectrumReceipt :
  HolographicContractSpectrumReceipt
canonicalHolographicContractSpectrumReceipt =
  holographicContractSpectrumReceipt
    true true true true true true true true true true

------------------------------------------------------------------------
-- Exact authority split.
------------------------------------------------------------------------

record HolographicContractEntropyAuthorityBoundary : Set where
  constructor holographicContractEntropyAuthorityBoundary
  field
    fullStateSpectralCalculationHasNativeLeanProducer : Bool
    fullDepthSameObjectEntropyWeldHasNativeLeanProducer : Bool
    factorizedSubsystemEntropyHasNativeLeanProducer : Bool
    leanKernelReceiptAttachedHere : Bool

    upstreamZModSubsystemFactorizationStillRequired : Bool
    subsystemReducedDensityMatrixStillRequired : Bool
    upstreamPartialTraceConstructionExists : Bool
    fullContractDoesNotByItselfProveDepthKSubsystemEntropy : Bool

    fullStateTheoremIsNotGenericPhysicalAdSCFT : Bool
    factorizedSubsystemTheoremIsNotUpstreamSameObjectByDefinition : Bool
    fullStateTheoremDoesNotIdentifyBirthmarkWithEntropy : Bool

canonicalHolographicContractEntropyAuthorityBoundary :
  HolographicContractEntropyAuthorityBoundary
canonicalHolographicContractEntropyAuthorityBoundary =
  holographicContractEntropyAuthorityBoundary
    true
    true
    true
    false
    true
    true
    false
    true
    true
    true
    true

------------------------------------------------------------------------
-- Named status surface used by regression/cross-lane consumers.
------------------------------------------------------------------------

holographicContractIsUniformDiagonal : Bool
holographicContractIsUniformDiagonal = true

uniformEigenvalueMultiplicity : Bool
uniformEigenvalueMultiplicity = true

uniformTraceNormalisation : Bool
uniformTraceNormalisation = true

fullContractVonNeumannEntropyIsNLogTwo : Bool
fullContractVonNeumannEntropyIsNLogTwo = true

fullStateEntropyMatchesTreeEntropyAtFullDepth : Bool
fullStateEntropyMatchesTreeEntropyAtFullDepth = true

factorizedSubsystemRTClosed : Bool
factorizedSubsystemRTClosed = true

upstreamZModSubsystemFactorizationStillRequired : Bool
upstreamZModSubsystemFactorizationStillRequired = true

subsystemReducedDensityMatrixStillRequired : Bool
subsystemReducedDensityMatrixStillRequired =
  upstreamZModSubsystemFactorizationStillRequired

fullContractDoesNotByItselfProveDepthKSubsystemEntropy : Bool
fullContractDoesNotByItselfProveDepthKSubsystemEntropy = true

fullStateEntropyReceiptRecorded :
  fullContractVonNeumannEntropyIsNLogTwo ≡ true
fullStateEntropyReceiptRecorded = refl

factorizedSubsystemReceiptRecorded :
  factorizedSubsystemRTClosed ≡ true
factorizedSubsystemReceiptRecorded = refl

upstreamSameObjectGapRemainsExplicit :
  upstreamZModSubsystemFactorizationStillRequired ≡ true
upstreamSameObjectGapRemainsExplicit = refl
