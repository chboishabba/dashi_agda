{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YMClayVaryingCarrierTransportParityExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.YMClayAristotleDonorAtlasExact as Atlas

------------------------------------------------------------------------
-- Aristotle 2026-09-17 varying-carrier transport parity.
--
-- Donor theorem family:
--   RequestProject/YangMills/VaryingCarrierTransport.lean
--
-- The checked Lean tranche transports a vacuum gap from cutoff Hamiltonians
-- living on genuinely different Hilbert spaces after embedding each finite
-- carrier isometrically into one common carrier.  Because the gap hypothesis is
-- stated intrinsically on each finite carrier, separate Hamiltonian
-- intertwining, vacuum-compatibility, and domain-preservation hypotheses are
-- not primitive inputs to that transport theorem.
--
-- This Agda owner records that theorem interface and its authority boundary. It
-- does not relabel the Lean theorem as an Agda kernel proof and it does not
-- construct the physical cutoff-to-continuum embedding family.
------------------------------------------------------------------------

record EmbeddingOnlyCarrierFamily : Set₁ where
  field
    Cutoff : Set
    CommonCarrier : Set
    FiniteCarrier : Cutoff → Set

    embed : (cutoff : Cutoff) → FiniteCarrier cutoff → CommonCarrier

    IsometricEmbedding : (cutoff : Cutoff) → Set
    isometricEmbedding : (cutoff : Cutoff) → IsometricEmbedding cutoff

open EmbeddingOnlyCarrierFamily public

varyingCarrierTransportLean : Atlas.LeanTheoremArtifact
varyingCarrierTransportLean = Atlas.varyingCarrierTransportLean

continuumWeldLean : Atlas.LeanTheoremArtifact
continuumWeldLean = Atlas.literalSU2ContinuumWeldLean

hamiltonianCompatibilityPrimitivePayment : Bool
hamiltonianCompatibilityPrimitivePayment = false

hamiltonianCompatibilityPrimitivePaymentIsFalse :
  hamiltonianCompatibilityPrimitivePayment ≡ false
hamiltonianCompatibilityPrimitivePaymentIsFalse = refl

vacuumCompatibilityPrimitivePayment : Bool
vacuumCompatibilityPrimitivePayment = false

vacuumCompatibilityPrimitivePaymentIsFalse :
  vacuumCompatibilityPrimitivePayment ≡ false
vacuumCompatibilityPrimitivePaymentIsFalse = refl

f2StructuralCarrierProblemPaidByEmbeddingTransport : Bool
f2StructuralCarrierProblemPaidByEmbeddingTransport = true

f2StructuralCarrierProblemPaidByEmbeddingTransportIsTrue :
  f2StructuralCarrierProblemPaidByEmbeddingTransport ≡ true
f2StructuralCarrierProblemPaidByEmbeddingTransportIsTrue = refl

varyingCarrierTransportLeanLevel : ProofLevel
varyingCarrierTransportLeanLevel = standardImported

varyingCarrierTransportNativeAgdaKernelLevel : ProofLevel
varyingCarrierTransportNativeAgdaKernelLevel = conditional

data VaryingCarrierTransportLeanDonorPresent : Set where
  varyingCarrierTransportLeanDonorPresent : VaryingCarrierTransportLeanDonorPresent

varyingCarrierTransportLeanDonorWitness : VaryingCarrierTransportLeanDonorPresent
varyingCarrierTransportLeanDonorWitness = varyingCarrierTransportLeanDonorPresent
