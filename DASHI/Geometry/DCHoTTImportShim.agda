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
import EqualityAndPaths as DCHoTTPath
open import Basics using (𝒰₀)
open import Im using (ℑ; ℑ-unit; ι)
open import FormalDisk using
  (_is-infinitesimally-close-to_
  ; _is-close-to_
  ; formal-disk-at_
  ; 𝔻
  ; 𝔻ᵣ
  ; inclusion-of-formal-disk-at
  ; induced-map-on-formal-disks
  ; push-forward
  ; d
  ; formal-disk-of)
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

data DCHoTTCompilationLane : Set where
  cohesionLane :
    DCHoTTCompilationLane

  cubicalLane :
    DCHoTTCompilationLane

  proofErasingInterfaceLane :
    DCHoTTCompilationLane

canonicalDCHoTTCompilationLanes :
  List DCHoTTCompilationLane
canonicalDCHoTTCompilationLanes =
  cohesionLane
  ∷ cubicalLane
  ∷ proofErasingInterfaceLane
  ∷ []

record DCHoTTFlagSplitArchitectureReceipt : Setω where
  field
    currentLocalFlagConflict :
      Bool

    currentLocalFlagConflictIsTrue :
      currentLocalFlagConflict ≡ true

    cohesionFlag :
      String

    cohesionFlag-v :
      cohesionFlag ≡ "--cohesion"

    cubicalFlag :
      String

    cubicalFlag-v :
      cubicalFlag ≡ "--cubical"

    incompatibleInCurrentLocalSetup :
      String

    incompatibleInCurrentLocalSetup-v :
      incompatibleInCurrentLocalSetup
      ≡
      "--cohesion and --cubical are incompatible in the current local Agda setup"

    separatelyCompiledModulesRequired :
      Bool

    separatelyCompiledModulesRequiredIsTrue :
      separatelyCompiledModulesRequired ≡ true

    bridgeInterface :
      String

    bridgeInterface-v :
      bridgeInterface
      ≡
      "proof-erasing interface carrying postulates/types between separately compiled cohesion and cubical modules"

    noCrossFlagImportInThisShim :
      Bool

    noCrossFlagImportInThisShimIsTrue :
      noCrossFlagImportInThisShim ≡ true

    lanes :
      List DCHoTTCompilationLane

    lanesAreCanonical :
      lanes ≡ canonicalDCHoTTCompilationLanes

    governanceBoundary :
      List String

open DCHoTTFlagSplitArchitectureReceipt public

canonicalDCHoTTFlagSplitArchitectureReceipt :
  DCHoTTFlagSplitArchitectureReceipt
canonicalDCHoTTFlagSplitArchitectureReceipt =
  record
    { currentLocalFlagConflict =
        true
    ; currentLocalFlagConflictIsTrue =
        refl
    ; cohesionFlag =
        "--cohesion"
    ; cohesionFlag-v =
        refl
    ; cubicalFlag =
        "--cubical"
    ; cubicalFlag-v =
        refl
    ; incompatibleInCurrentLocalSetup =
        "--cohesion and --cubical are incompatible in the current local Agda setup"
    ; incompatibleInCurrentLocalSetup-v =
        refl
    ; separatelyCompiledModulesRequired =
        true
    ; separatelyCompiledModulesRequiredIsTrue =
        refl
    ; bridgeInterface =
        "proof-erasing interface carrying postulates/types between separately compiled cohesion and cubical modules"
    ; bridgeInterface-v =
        refl
    ; noCrossFlagImportInThisShim =
        true
    ; noCrossFlagImportInThisShimIsTrue =
        refl
    ; lanes =
        canonicalDCHoTTCompilationLanes
    ; lanesAreCanonical =
        refl
    ; governanceBoundary =
        "compile DCHoTT/cohesive surfaces in a cohesion-lane module"
        ∷ "compile cubical quotient/path surfaces in a cubical-lane module"
        ∷ "connect the lanes only through proof-erasing postulated/type interfaces"
        ∷ "do not import a --cubical module from this --without-K DCHoTT shim"
        ∷ "do not add global flags that force --cohesion and --cubical into one module"
        ∷ []
    }

postulate
  DCHoTTModelCarrier :
    𝒰₀

  DCHoTTModelBasePoint :
    DCHoTTModelCarrier

  DCHoTTHomogeneousModel :
    homogeneous-structure-on DCHoTTModelCarrier

  DCHoTTManifoldSocket :
    DCHoTTHomogeneousModel -manifold

DCHoTTInfinitesimalShape :
  𝒰₀ →
  𝒰₀
DCHoTTInfinitesimalShape =
  ℑ

DCHoTTInfinitesimalUnit :
  {X : 𝒰₀} →
  X →
  DCHoTTInfinitesimalShape X
DCHoTTInfinitesimalUnit =
  ℑ-unit

DCHoTTCoreducedPoint :
  {X : 𝒰₀} →
  X →
  DCHoTTInfinitesimalShape X
DCHoTTCoreducedPoint =
  ι

DCHoTTPathOver :
  {X : 𝒰₀} →
  X →
  X →
  𝒰₀
DCHoTTPathOver =
  DCHoTTPath._≈_

DCHoTTBuiltinEqualityToPath :
  {X : 𝒰₀} →
  {x y : X} →
  x
  ≡
  y →
  DCHoTTPathOver x y
DCHoTTBuiltinEqualityToPath refl =
  DCHoTTPath.refl

DCHoTTApplyToPath :
  {X Y : 𝒰₀} →
  {x y : X} →
  (f : X → Y) →
  DCHoTTPathOver x y →
  DCHoTTPathOver (f x) (f y)
DCHoTTApplyToPath =
  DCHoTTPath._⁎_

DCHoTTEqualityToImPath :
  {X : 𝒰₀} →
  {x y : X} →
  x
  ≡
  y →
  DCHoTTPathOver
    (DCHoTTInfinitesimalUnit x)
    (DCHoTTInfinitesimalUnit y)
DCHoTTEqualityToImPath eq =
  DCHoTTApplyToPath
    DCHoTTInfinitesimalUnit
    (DCHoTTBuiltinEqualityToPath eq)

DCHoTTInfinitesimalProximity :
  {X : 𝒰₀} →
  X →
  X →
  𝒰₀
DCHoTTInfinitesimalProximity x y =
  x is-infinitesimally-close-to y

DCHoTTCloseTo :
  {X : 𝒰₀} →
  X →
  X →
  𝒰₀
DCHoTTCloseTo x y =
  x is-close-to y

DCHoTTFormalDiskAt :
  {X : 𝒰₀} →
  X →
  𝒰₀
DCHoTTFormalDiskAt x =
  formal-disk-at x

DCHoTTFormalDisk :
  (X : 𝒰₀) →
  X →
  𝒰₀
DCHoTTFormalDisk X x =
  𝔻 X x

DCHoTTReducedFormalDisk :
  (X : 𝒰₀) →
  DCHoTTInfinitesimalShape X →
  𝒰₀
DCHoTTReducedFormalDisk X x =
  𝔻ᵣ X x

DCHoTTFormalDiskInclusion :
  {X : 𝒰₀} →
  (x : X) →
  DCHoTTFormalDiskAt x →
  X
DCHoTTFormalDiskInclusion =
  inclusion-of-formal-disk-at

DCHoTTInducedFormalDiskMap :
  {X Y : 𝒰₀} →
  (f : X → Y) →
  (x : X) →
  DCHoTTFormalDisk X x →
  DCHoTTFormalDisk Y (f x)
DCHoTTInducedFormalDiskMap =
  induced-map-on-formal-disks

DCHoTTPushForward :
  {X Y : 𝒰₀} →
  (f : X → Y) →
  (x : X) →
  DCHoTTFormalDisk X x →
  DCHoTTFormalDisk Y (f x)
DCHoTTPushForward =
  push-forward

DCHoTTDifferential :
  {X Y : 𝒰₀} →
  (f : X → Y) →
  (x : X) →
  DCHoTTFormalDisk X x →
  DCHoTTFormalDisk Y (f x)
DCHoTTDifferential =
  d

DCHoTTFormalDiskOfHomogeneous :
  {V : 𝒰₀} →
  homogeneous-structure-on V →
  𝒰₀
DCHoTTFormalDiskOfHomogeneous =
  formal-disk-of

DCHoTTFormalDiskAtModelBasePointSocket :
  𝒰₀
DCHoTTFormalDiskAtModelBasePointSocket =
  DCHoTTFormalDiskAt DCHoTTModelBasePoint

DCHoTTImModelSocket :
  𝒰₀
DCHoTTImModelSocket =
  DCHoTTInfinitesimalShape DCHoTTModelCarrier

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

    dependencyCommit :
      String

    agdaVersionCompatibility :
      String

    stdlibCompatibility :
      String

    licenseStatus :
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

    formalDiskSurfaceVisible :
      Bool

    formalDiskSurfaceVisibleIsTrue :
      formalDiskSurfaceVisible ≡ true

    imSurfaceVisible :
      Bool

    imSurfaceVisibleIsTrue :
      imSurfaceVisible ≡ true

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

    flagSplitArchitecture :
      DCHoTTFlagSplitArchitectureReceipt

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
        "flat root modules: Basics, Im, FormalDisk, Manifolds, FormalDiskBundle, G-structure"
    ; dependencyCommit =
        "ca8c755af0b26f8f50c5a60d3b7f9384a26f5d0e"
    ; agdaVersionCompatibility =
        "DCHoTT-Agda README target Agda 2.6.2.2; shim typechecked locally under Agda 2.6.4.3"
    ; stdlibCompatibility =
        "DASHI build uses standard-library-2.0 via /usr/share/agda/lib/standard-library.agda-lib"
    ; licenseStatus =
        "no license file found in DCHoTT-Agda clone root; redistribution status remains an intake item"
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
    ; formalDiskSurfaceVisible =
        true
    ; formalDiskSurfaceVisibleIsTrue =
        refl
    ; imSurfaceVisible =
        true
    ; imSurfaceVisibleIsTrue =
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
    ; flagSplitArchitecture =
        canonicalDCHoTTFlagSplitArchitectureReceipt
    ; visibleExternalSurfaces =
        "ℑ"
        ∷ "ℑ-unit"
        ∷ "DCHoTT _≈_ path"
        ∷ "builtin equality -> DCHoTT path"
        ∷ "builtin equality -> DCHoTT Im path"
        ∷ "formal-disk-at_"
        ∷ "𝔻"
        ∷ "𝔻ᵣ"
        ∷ "_is-infinitesimally-close-to_"
        ∷ "induced-map-on-formal-disks"
        ∷ "push-forward"
        ∷ "d"
        ∷ "homogeneous-structure-on_"
        ∷ "_-manifold"
        ∷ "formal-disk-bundle"
        ∷ "groups-over-automorphismgroup-of_"
        ∷ []
    ; governanceBoundary =
        "DCHoTT dependency intake and flat import resolution are complete"
        ∷ "DCHoTT-Agda does not expose a DCHoTT.* namespace in this clone"
        ∷ "Im and FormalDisk are imported through actual local flat modules and exposed as DASHI shim aliases"
        ∷ "DCHoTT path and equality-to-Im-path helpers are exposed only as shim adapters over the local EqualityAndPaths module"
        ∷ "--cohesion and --cubical are locally incompatible and must remain in separately compiled modules"
        ∷ "cross-lane connection is by proof-erasing postulates/types, not by direct mixed-flag imports"
        ∷ "this shim uses postulated sockets only to name bridge targets"
        ∷ "no torsion-free G-structure specialisation, Levi-Civita adapter, or B0 theorem is imported here"
        ∷ []
    }
