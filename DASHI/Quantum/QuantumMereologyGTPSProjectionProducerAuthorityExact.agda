{-# OPTIONS --safe #-}
module DASHI.Quantum.QuantumMereologyGTPSProjectionProducerAuthorityExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Quantum.QuantumMereologySourceAtlasExact as Sources

record GTPSProjectionProducerStatus : Set where
  field
    FiniteHilbertSchmidtCarrierSourceWritten : Bool
    FiniteHilbertSchmidtCarrierSourceWrittenIsTrue :
      FiniteHilbertSchmidtCarrierSourceWritten ≡ true

    FiniteHilbertSchmidtProjectorSourceWritten : Bool
    FiniteHilbertSchmidtProjectorSourceWrittenIsTrue :
      FiniteHilbertSchmidtProjectorSourceWritten ≡ true

    FiniteAlgebraProjectorSourceWritten : Bool
    FiniteAlgebraProjectorSourceWrittenIsTrue :
      FiniteAlgebraProjectorSourceWritten ≡ true

    FiniteSourceGTPSShortTimeScoreInstantiated : Bool
    FiniteSourceGTPSShortTimeScoreInstantiatedIsTrue :
      FiniteSourceGTPSShortTimeScoreInstantiated ≡ true

    FiniteSourceGTPSAlgebraDistanceInstantiated : Bool
    FiniteSourceGTPSAlgebraDistanceInstantiatedIsTrue :
      FiniteSourceGTPSAlgebraDistanceInstantiated ≡ true

    PhysicalSourceGTPSAutomaticallyIdentified : Bool
    PhysicalSourceGTPSAutomaticallyIdentifiedIsFalse :
      PhysicalSourceGTPSAutomaticallyIdentified ≡ false

    PhysicalHamiltonianAutomaticallyAttached : Bool
    PhysicalHamiltonianAutomaticallyAttachedIsFalse :
      PhysicalHamiltonianAutomaticallyAttached ≡ false

canonicalGTPSProjectionProducerStatus : GTPSProjectionProducerStatus
canonicalGTPSProjectionProducerStatus = record
  { FiniteHilbertSchmidtCarrierSourceWritten = true
  ; FiniteHilbertSchmidtCarrierSourceWrittenIsTrue = refl
  ; FiniteHilbertSchmidtProjectorSourceWritten = true
  ; FiniteHilbertSchmidtProjectorSourceWrittenIsTrue = refl
  ; FiniteAlgebraProjectorSourceWritten = true
  ; FiniteAlgebraProjectorSourceWrittenIsTrue = refl
  ; FiniteSourceGTPSShortTimeScoreInstantiated = true
  ; FiniteSourceGTPSShortTimeScoreInstantiatedIsTrue = refl
  ; FiniteSourceGTPSAlgebraDistanceInstantiated = true
  ; FiniteSourceGTPSAlgebraDistanceInstantiatedIsTrue = refl
  ; PhysicalSourceGTPSAutomaticallyIdentified = false
  ; PhysicalSourceGTPSAutomaticallyIdentifiedIsFalse = refl
  ; PhysicalHamiltonianAutomaticallyAttached = false
  ; PhysicalHamiltonianAutomaticallyAttachedIsFalse = refl
  }

mathlibFiniteProjectionSourceReceipt : Sources.AttributionReceipt
mathlibFiniteProjectionSourceReceipt =
  Sources.attribution-receipt
    Sources.importedFormalTheoremSource
    "mathlib v4.28.0: EuclideanSpace/PiLp and Submodule.HasOrthogonalProjection.ofCompleteSpace"
    "Provides the finite L2 inner-product carrier and canonical orthogonal projection onto complete finite-dimensional subspaces."

leanGTPSProjectionProducerSourceReceipt : Sources.AttributionReceipt
leanGTPSProjectionProducerSourceReceipt =
  Sources.attribution-receipt
    Sources.importedFormalTheoremSource
    "DASHI Lean: QuantumMereologyGTPSProjectionProducer"
    "Source-written Lean theorem surface flattening finite complex matrices into Euclidean Hilbert--Schmidt coordinates, constructing the finite A and A+A' subspaces, and instantiating the source short-time and algebra-distance orthogonal projectors. This is source authority only until exact-head Lean kernel evidence exists."

dashiGTPSProjectionCrossModuleReceipt : Sources.AttributionReceipt
dashiGTPSProjectionCrossModuleReceipt =
  Sources.attribution-receipt
    Sources.crossModuleInference
    "DASHI Agda"
    "Records that finite mathematical projector existence is no longer a source/physics input while retaining physical source-gTPS and Hamiltonian identification as separate unpaid same-object obligations."
