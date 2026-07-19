module DASHI.Applied.Seaminit.KernelCoupling where

open import Agda.Builtin.Bool     using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat      using (Nat)
open import Agda.Builtin.Sigma    using (Σ; _,_)

------------------------------------------------------------------------
-- Core carriers

record BodyGeometry : Set₁ where
  field
    Vertex      : Set
    Face        : Set
    Pose        : Set
    restVertex  : Vertex → Set
    faceWitness : Face → Set
    deform      : Pose → Vertex → Vertex

record ROMKernel (Pose : Set) : Set₁ where
  field
    Feature        : Set
    Path           : Set
    Debt           : Set
    feature        : Pose → Feature
    admissible     : Pose → Bool
    pathStart      : Path → Pose
    pathEnd        : Path → Pose
    loadCocycle    : Path → Debt

record FabricKernel : Set₁ where
  field
    Fabric          : Set
    FabricFeature   : Set
    feature         : Fabric → FabricFeature
    admissible      : Fabric → Bool

record BodyBasis (Vertex Coeff Field : Set) : Set₁ where
  field
    basisSize       : Nat
    project         : Coeff → Vertex → Field
    reconstruct     : (Vertex → Field) → Coeff

------------------------------------------------------------------------
-- Coupled coefficient model

record CoefficientCoupler
  (PoseFeature FabricFeature Coeff : Set) : Set₁ where
  field
    poseOnly        : PoseFeature → Coeff
    fabricOnly      : FabricFeature → Coeff
    interaction     : PoseFeature → FabricFeature → Coeff
    combine3        : Coeff → Coeff → Coeff → Coeff

  coupled : PoseFeature → FabricFeature → Coeff
  coupled q p = combine3 (poseOnly q) (fabricOnly p) (interaction q p)

------------------------------------------------------------------------
-- Shared-basis body fields

record FieldFamily
  (Pose Fabric Vertex Coeff Field : Set)
  (rom : ROMKernel Pose)
  (fab : FabricKernel)
  (basis : BodyBasis Vertex Coeff Field)
  (coupler : CoefficientCoupler
    (ROMKernel.Feature rom)
    (FabricKernel.FabricFeature fab)
    Coeff)
  : Set₁ where

  private
    module R = ROMKernel rom
    module F = FabricKernel fab
    module B = BodyBasis basis
    module C = CoefficientCoupler coupler

  field
    tensionCoeff : Pose → Fabric → Coeff
    pressureCoeff : Pose → Fabric → Coeff
    shearCoeff : Pose → Fabric → Coeff
    supportCoeff : Pose → Fabric → Coeff

    tensionUsesCoupling : ∀ q p →
      tensionCoeff q p ≡ C.coupled (R.feature q) (F.feature p)

  tension : Pose → Fabric → Vertex → Field
  tension q p = B.project (tensionCoeff q p)

  pressure : Pose → Fabric → Vertex → Field
  pressure q p = B.project (pressureCoeff q p)

  shear : Pose → Fabric → Vertex → Field
  shear q p = B.project (shearCoeff q p)

  support : Pose → Fabric → Vertex → Field
  support q p = B.project (supportCoeff q p)

------------------------------------------------------------------------
-- Transport and projection contracts

record ProjectionContract
  (Pose Vertex Coeff Field : Set)
  (basis : BodyBasis Vertex Coeff Field)
  : Set₁ where

  private
    module B = BodyBasis basis

  field
    transportVertex : Pose → Vertex → Vertex
    vertexIdentityStable : ∀ q v → transportVertex q v ≡ transportVertex q v
    reconstructProject : ∀ z → B.reconstruct (B.project z) ≡ z

projection-roundtrip :
  ∀ {Pose Vertex Coeff Field}
  {basis : BodyBasis Vertex Coeff Field}
  (C : ProjectionContract Pose Vertex Coeff Field basis)
  (z : Coeff) →
  BodyBasis.reconstruct basis (BodyBasis.project basis z) ≡ z
projection-roundtrip C z = ProjectionContract.reconstructProject C z

------------------------------------------------------------------------
-- A complete runtime bundle: one engine, many output surfaces.

record SeaminitKernelEngine : Set₂ where
  field
    Pose          : Set
    Fabric        : Set
    Vertex        : Set
    Coeff         : Set
    Field         : Set

    geometry      : BodyGeometry
    rom           : ROMKernel Pose
    fabricKernel  : FabricKernel
    basis         : BodyBasis Vertex Coeff Field
    coupler       : CoefficientCoupler
      (ROMKernel.Feature rom)
      (FabricKernel.FabricFeature fabricKernel)
      Coeff

    fields        : FieldFamily
      Pose Fabric Vertex Coeff Field
      rom fabricKernel basis coupler

    projectionLaw : ProjectionContract Pose Vertex Coeff Field basis

  bodyField : Pose → Fabric → Vertex → Field
  bodyField = FieldFamily.support fields

  coefficientRoundtrip : ∀ z →
    BodyBasis.reconstruct basis (BodyBasis.project basis z) ≡ z
  coefficientRoundtrip = ProjectionContract.reconstructProject projectionLaw
