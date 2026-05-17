{-# OPTIONS --without-K #-}

module DASHI.Geometry.DCHoTTImportShim where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

-- DCHoTT-Agda is an older flat-module Agda repository.  The modules are
-- imported by their file names from the DCHoTT-Agda include path, not through a
-- DCHoTT.* namespace.
open import Basics using (𝒰₀)
open import HomogeneousType using (homogeneous-structure-on_)
open import Manifolds using (_-manifold)
open import FormalDiskBundle using (formal-disk-bundle)
open import G-structure using (groups-over-automorphismgroup-of_)

------------------------------------------------------------------------
-- Minimal dependency-intake shim.
--
-- This module proves only that DASHI can see the relevant DCHoTT surfaces in
-- the local Agda build.  It deliberately does not claim a torsion-free
-- G-structure theorem, a Levi-Civita adapter, or the B0 emergence theorem.

postulate
  DCHoTTModelCarrier :
    𝒰₀

  DCHoTTHomogeneousModel :
    homogeneous-structure-on DCHoTTModelCarrier

  DCHoTTManifoldSocket :
    DCHoTTHomogeneousModel -manifold

DCHoTTFormalDiskBundleSocket :
  𝒰₀
DCHoTTFormalDiskBundleSocket =
  formal-disk-bundle DCHoTTModelCarrier

postulate
  DCHoTTGroupOverAutomorphismSocket :
    groups-over-automorphismgroup-of DCHoTTFormalDiskBundleSocket

record DCHoTTImportShimReceipt : Setω where
  field
    dependencyPath :
      String

    actualModuleLayout :
      String

    importsResolve :
      Bool

    importsResolveIsTrue :
      importsResolve ≡ true

    manifoldSurfaceVisible :
      Bool

    manifoldSurfaceVisibleIsTrue :
      manifoldSurfaceVisible ≡ true

    formalDiskBundleSurfaceVisible :
      Bool

    formalDiskBundleSurfaceVisibleIsTrue :
      formalDiskBundleSurfaceVisible ≡ true

    gStructureSurfaceVisible :
      Bool

    gStructureSurfaceVisibleIsTrue :
      gStructureSurfaceVisible ≡ true

    torsionFreeLeviCivitaAdapterImported :
      Bool

    torsionFreeLeviCivitaAdapterImportedIsFalse :
      torsionFreeLeviCivitaAdapterImported ≡ false

    b0EmergenceTheoremImported :
      Bool

    b0EmergenceTheoremImportedIsFalse :
      b0EmergenceTheoremImported ≡ false

    noPhysicsPromotionFromThisShim :
      Bool

    noPhysicsPromotionFromThisShimIsTrue :
      noPhysicsPromotionFromThisShim ≡ true

    visibleExternalSurfaces :
      List String

    governanceBoundary :
      List String

open DCHoTTImportShimReceipt public

canonicalDCHoTTImportShimReceipt :
  DCHoTTImportShimReceipt
canonicalDCHoTTImportShimReceipt =
  record
    { dependencyPath =
        "DCHoTT-Agda"
    ; actualModuleLayout =
        "flat root modules: Basics, Manifolds, FormalDiskBundle, G-structure"
    ; importsResolve =
        true
    ; importsResolveIsTrue =
        refl
    ; manifoldSurfaceVisible =
        true
    ; manifoldSurfaceVisibleIsTrue =
        refl
    ; formalDiskBundleSurfaceVisible =
        true
    ; formalDiskBundleSurfaceVisibleIsTrue =
        refl
    ; gStructureSurfaceVisible =
        true
    ; gStructureSurfaceVisibleIsTrue =
        refl
    ; torsionFreeLeviCivitaAdapterImported =
        false
    ; torsionFreeLeviCivitaAdapterImportedIsFalse =
        refl
    ; b0EmergenceTheoremImported =
        false
    ; b0EmergenceTheoremImportedIsFalse =
        refl
    ; noPhysicsPromotionFromThisShim =
        true
    ; noPhysicsPromotionFromThisShimIsTrue =
        refl
    ; visibleExternalSurfaces =
        "homogeneous-structure-on_"
        ∷ "_-manifold"
        ∷ "formal-disk-bundle"
        ∷ "groups-over-automorphismgroup-of_"
        ∷ []
    ; governanceBoundary =
        "DCHoTT dependency intake and flat import resolution are complete"
        ∷ "DCHoTT-Agda does not expose a DCHoTT.* namespace in this clone"
        ∷ "this shim uses postulated sockets only to name bridge targets"
        ∷ "no torsion-free G-structure specialisation, Levi-Civita adapter, or B0 theorem is imported here"
        ∷ []
    }
