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
-- constant diagonal entry 2^(-n).  Hence its spectrum is the uniform spectrum
-- with multiplicity 2^n and its full-state von-Neumann entropy is n log 2.
--
-- A native Mathlib producer for that spectral calculation is maintained in
-- dashi_lean4/Synthesis/HolographicContractEntropy.lean (PR #68).  This Agda
-- owner records the exact cross-repo theorem shape and, crucially, separates
-- the now-closed full-state calculation from the still-distinct depth-k
-- reduced-density-matrix / partial-trace theorem.
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

canonicalHolographicContractSpectrumReceipt :
  HolographicContractSpectrumReceipt
canonicalHolographicContractSpectrumReceipt =
  holographicContractSpectrumReceipt
    true true true true true true true true

------------------------------------------------------------------------
-- Exact authority split.
------------------------------------------------------------------------

record HolographicContractEntropyAuthorityBoundary : Set where
  constructor holographicContractEntropyAuthorityBoundary
  field
    fullStateSpectralCalculationHasNativeLeanProducer : Bool
    fullDepthSameObjectEntropyWeldHasNativeLeanProducer : Bool
    leanKernelReceiptAttachedHere : Bool

    subsystemReducedDensityMatrixStillRequired : Bool
    upstreamPartialTraceConstructionExists : Bool
    fullContractDoesNotByItselfProveDepthKSubsystemEntropy : Bool

    fullStateTheoremIsNotGenericPhysicalAdSCFT : Bool
    fullStateTheoremDoesNotIdentifyBirthmarkWithEntropy : Bool
    subsystemClaimMustNotBePromotedFromFullStateClaim : Bool

canonicalHolographicContractEntropyAuthorityBoundary :
  HolographicContractEntropyAuthorityBoundary
canonicalHolographicContractEntropyAuthorityBoundary =
  holographicContractEntropyAuthorityBoundary
    true
    true
    false
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

subsystemReducedDensityMatrixStillRequired : Bool
subsystemReducedDensityMatrixStillRequired = true

fullContractDoesNotByItselfProveDepthKSubsystemEntropy : Bool
fullContractDoesNotByItselfProveDepthKSubsystemEntropy = true

fullStateEntropyReceiptRecorded :
  fullContractVonNeumannEntropyIsNLogTwo ≡ true
fullStateEntropyReceiptRecorded = refl

subsystemGapRemainsExplicit :
  subsystemReducedDensityMatrixStillRequired ≡ true
subsystemGapRemainsExplicit = refl
