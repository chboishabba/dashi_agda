{-# OPTIONS --safe #-}
module DASHI.Quantum.QuantumMereologyInnerProductTPSAuthorityExact where

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Quantum.QuantumMereologyExact as QM
import DASHI.Quantum.QuantumMereologyFiniteLinearTPSAuthorityExact as Linear
import DASHI.Quantum.QuantumMereologySourceAtlasExact as Sources

------------------------------------------------------------------------
-- AGDA AUTHORITY SOCKET FOR INNER-PRODUCT TPS RECONSTRUCTION
--
-- The current Agda quantum carrier has no concrete tensor-product inner-product
-- construction.  The Lean/mathlib theorem source is therefore represented only
-- as explicit imported authority, never reconstructed by naming.
------------------------------------------------------------------------

record InnerProductTPSAuthority
    (W : QM.BareQuantumWorld)
    (T : QM.TensorProductStructure W) : Set₁ where
  field
    linearAuthority :
      Linear.FiniteLinearTPSAuthority W T

    InnerProductReconstructionAuthority : Set
    innerProductReconstructionAuthority :
      InnerProductReconstructionAuthority

    NormPreservationAuthority : Set
    normPreservationAuthority :
      NormPreservationAuthority

open InnerProductTPSAuthority public

record InnerProductTPSPromotionBoundary : Set where
  field
    importedIsometryCreatesAgdaTensorProduct : Bool
    importedIsometryCreatesAgdaTensorProductIsFalse :
      importedIsometryCreatesAgdaTensorProduct ≡ false

    importedIsometryCreatesCompletedHilbertTensorProduct : Bool
    importedIsometryCreatesCompletedHilbertTensorProductIsFalse :
      importedIsometryCreatesCompletedHilbertTensorProduct ≡ false

    importedIsometryCreatesHamiltonianLocality : Bool
    importedIsometryCreatesHamiltonianLocalityIsFalse :
      importedIsometryCreatesHamiltonianLocality ≡ false

    importedIsometrySelectsPreferredTPS : Bool
    importedIsometrySelectsPreferredTPSIsFalse :
      importedIsometrySelectsPreferredTPS ≡ false

canonicalInnerProductTPSPromotionBoundary :
  InnerProductTPSPromotionBoundary
canonicalInnerProductTPSPromotionBoundary = record
  { importedIsometryCreatesAgdaTensorProduct = false
  ; importedIsometryCreatesAgdaTensorProductIsFalse = refl
  ; importedIsometryCreatesCompletedHilbertTensorProduct = false
  ; importedIsometryCreatesCompletedHilbertTensorProductIsFalse = refl
  ; importedIsometryCreatesHamiltonianLocality = false
  ; importedIsometryCreatesHamiltonianLocalityIsFalse = refl
  ; importedIsometrySelectsPreferredTPS = false
  ; importedIsometrySelectsPreferredTPSIsFalse = refl
  }

leanInnerProductTPSSourceWrittenReceipt : Sources.AttributionReceipt
leanInnerProductTPSSourceWrittenReceipt =
  Sources.attribution-receipt
    Sources.importedFormalTheoremSource
    "DASHI Lean: RequestProject.QuantumMereologyInnerProductTPS"
    "Source-written Lean owner using mathlib v4.28.0 tensor-product inner-product/isometry theorems. This is source lineage only until an exact-head Lean kernel/build receipt exists."

agdaInnerProductTPSAuthoritySocketReceipt : Sources.AttributionReceipt
agdaInnerProductTPSAuthoritySocketReceipt =
  Sources.attribution-receipt
    Sources.crossModuleInference
    "DASHI Agda"
    "Agda exposes only explicit inner-product/norm authority sockets layered over the finite-linear TPS authority; no tensor-product metric construction is manufactured locally."
