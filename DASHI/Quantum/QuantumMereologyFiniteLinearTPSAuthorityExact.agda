{-# OPTIONS --safe #-}
module DASHI.Quantum.QuantumMereologyFiniteLinearTPSAuthorityExact where

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _*_)

import DASHI.Quantum.QuantumMereologyExact as QM
import DASHI.Quantum.QuantumMereologySourceAtlasExact as Sources

------------------------------------------------------------------------
-- AGDA AUTHORITY SOCKET FOR THE LEAN FINITE LINEAR TPS THEOREM
--
-- Agda's current Hilbert skeleton has no concrete tensor-product construction.
-- This module therefore does NOT manufacture one. It states exactly what a
-- cross-prover consumer may import once the Lean theorem source is independently
-- checked/pinned.
------------------------------------------------------------------------

record FiniteLinearTPSAuthority
    (W : QM.BareQuantumWorld)
    (T : QM.TensorProductStructure W) : Set₁ where
  field
    leftDimension rightDimension ambientDimension : Nat

    dimensionProduct :
      ambientDimension ≡ leftDimension * rightDimension

    LinearTensorReconstructionAuthority : Set
    linearTensorReconstructionAuthority :
      LinearTensorReconstructionAuthority

open FiniteLinearTPSAuthority public

record FiniteLinearTPSPromotionBoundary : Set where
  field
    dimensionProductConstructsTensorProductInAgda : Bool
    dimensionProductConstructsTensorProductInAgdaIsFalse :
      dimensionProductConstructsTensorProductInAgda ≡ false

    linearAuthorityCreatesHilbertIsometry : Bool
    linearAuthorityCreatesHilbertIsometryIsFalse :
      linearAuthorityCreatesHilbertIsometry ≡ false

    linearAuthorityCreatesHamiltonianLocality : Bool
    linearAuthorityCreatesHamiltonianLocalityIsFalse :
      linearAuthorityCreatesHamiltonianLocality ≡ false

    linearAuthoritySelectsPreferredTPS : Bool
    linearAuthoritySelectsPreferredTPSIsFalse :
      linearAuthoritySelectsPreferredTPS ≡ false

canonicalFiniteLinearTPSPromotionBoundary :
  FiniteLinearTPSPromotionBoundary
canonicalFiniteLinearTPSPromotionBoundary = record
  { dimensionProductConstructsTensorProductInAgda = false
  ; dimensionProductConstructsTensorProductInAgdaIsFalse = refl
  ; linearAuthorityCreatesHilbertIsometry = false
  ; linearAuthorityCreatesHilbertIsometryIsFalse = refl
  ; linearAuthorityCreatesHamiltonianLocality = false
  ; linearAuthorityCreatesHamiltonianLocalityIsFalse = refl
  ; linearAuthoritySelectsPreferredTPS = false
  ; linearAuthoritySelectsPreferredTPSIsFalse = refl
  }

leanFiniteLinearTPSSourceWrittenReceipt : Sources.AttributionReceipt
leanFiniteLinearTPSSourceWrittenReceipt =
  Sources.attribution-receipt
    Sources.importedFormalTheoremSource
    "DASHI Lean: RequestProject.QuantumMereologyFiniteLinearTPS"
    "Source-written Lean owner for a complex-linear bipartite tensor reconstruction and its finrank product theorem. This receipt records source lineage only; it is not an exact-head Lean kernel/build receipt."

agdaFiniteLinearTPSAuthoritySocketReceipt : Sources.AttributionReceipt
agdaFiniteLinearTPSAuthoritySocketReceipt =
  Sources.attribution-receipt
    Sources.crossModuleInference
    "DASHI Agda"
    "Agda consumes only a typed finite-linear-TPS authority socket and dimension-product witness; it does not reconstruct mathlib's tensor product or promote the Lean source to Hilbert/physical authority."
