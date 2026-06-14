module DASHI.Geometry.DifferentialGeometryParity where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; _∷_; [])
open import Agda.Builtin.String using (String)

data ⊥ : Set where

------------------------------------------------------------------------
-- Differential-geometry parity layer.
--
-- This module records the checked DASHI-side parity surface for the
-- PhysLean differential-geometry vocabulary.  It names the interfaces and
-- standard identity obligations that downstream work must discharge, but it
-- deliberately does not assert imported theorem authority.  The canonical
-- receipt is fail-closed: every theorem/promotion flag is explicit and false
-- unless a constructorless authority token is supplied from outside.

data DifferentialGeometryParityStatus : Set where
  differentialGeometryTargetsOnlyNoPromotion :
    DifferentialGeometryParityStatus

data DifferentialGeometryConcept : Set where
  manifoldConcept :
    DifferentialGeometryConcept

  smoothMapConcept :
    DifferentialGeometryConcept

  tangentBundleConcept :
    DifferentialGeometryConcept

  cotangentBundleConcept :
    DifferentialGeometryConcept

  differentialFormConcept :
    DifferentialGeometryConcept

  vectorFieldConcept :
    DifferentialGeometryConcept

  metricConcept :
    DifferentialGeometryConcept

  connectionConcept :
    DifferentialGeometryConcept

  curvatureConcept :
    DifferentialGeometryConcept

data DifferentialGeometryIdentityTarget : Set where
  exteriorDerivativeSquaresToZeroTarget :
    DifferentialGeometryIdentityTarget

  cartanFormulaTarget :
    DifferentialGeometryIdentityTarget

  stokesTheoremTarget :
    DifferentialGeometryIdentityTarget

  poincareLemmaTarget :
    DifferentialGeometryIdentityTarget

  bianchiIdentityTarget :
    DifferentialGeometryIdentityTarget

data DifferentialGeometryOpenObligation : Set where
  missingManifoldAdapter :
    DifferentialGeometryOpenObligation

  missingSmoothMapAdapter :
    DifferentialGeometryOpenObligation

  missingTangentBundleAdapter :
    DifferentialGeometryOpenObligation

  missingCotangentBundleAdapter :
    DifferentialGeometryOpenObligation

  missingDifferentialFormAdapter :
    DifferentialGeometryOpenObligation

  missingVectorFieldAdapter :
    DifferentialGeometryOpenObligation

  missingMetricAdapter :
    DifferentialGeometryOpenObligation

  missingConnectionAdapter :
    DifferentialGeometryOpenObligation

  missingCurvatureAdapter :
    DifferentialGeometryOpenObligation

  missingExteriorDerivativeSquaresToZeroProof :
    DifferentialGeometryOpenObligation

  missingCartanFormulaProof :
    DifferentialGeometryOpenObligation

  missingStokesTheoremProof :
    DifferentialGeometryOpenObligation

  missingPoincareLemmaProof :
    DifferentialGeometryOpenObligation

  missingBianchiIdentityProof :
    DifferentialGeometryOpenObligation

  missingPhysLeanParityAuthority :
    DifferentialGeometryOpenObligation

canonicalDifferentialGeometryConcepts :
  List DifferentialGeometryConcept
canonicalDifferentialGeometryConcepts =
  manifoldConcept
  ∷ smoothMapConcept
  ∷ tangentBundleConcept
  ∷ cotangentBundleConcept
  ∷ differentialFormConcept
  ∷ vectorFieldConcept
  ∷ metricConcept
  ∷ connectionConcept
  ∷ curvatureConcept
  ∷ []

canonicalDifferentialGeometryIdentityTargets :
  List DifferentialGeometryIdentityTarget
canonicalDifferentialGeometryIdentityTargets =
  exteriorDerivativeSquaresToZeroTarget
  ∷ cartanFormulaTarget
  ∷ stokesTheoremTarget
  ∷ poincareLemmaTarget
  ∷ bianchiIdentityTarget
  ∷ []

canonicalDifferentialGeometryOpenObligations :
  List DifferentialGeometryOpenObligation
canonicalDifferentialGeometryOpenObligations =
  missingManifoldAdapter
  ∷ missingSmoothMapAdapter
  ∷ missingTangentBundleAdapter
  ∷ missingCotangentBundleAdapter
  ∷ missingDifferentialFormAdapter
  ∷ missingVectorFieldAdapter
  ∷ missingMetricAdapter
  ∷ missingConnectionAdapter
  ∷ missingCurvatureAdapter
  ∷ missingExteriorDerivativeSquaresToZeroProof
  ∷ missingCartanFormulaProof
  ∷ missingStokesTheoremProof
  ∷ missingPoincareLemmaProof
  ∷ missingBianchiIdentityProof
  ∷ missingPhysLeanParityAuthority
  ∷ []

-- Constructorless: this module cannot manufacture parity promotion authority.
data DifferentialGeometryParityAuthorityToken : Set where

record CoreDifferentialGeometryInterfaceSurface : Setω where
  field
    Manifold :
      Set

    SmoothMap :
      Manifold →
      Manifold →
      Set

    TangentBundle :
      Manifold →
      Set

    CotangentBundle :
      Manifold →
      Set

    DifferentialForm :
      Manifold →
      Set

    VectorField :
      Manifold →
      Set

    Metric :
      Manifold →
      Set

    Connection :
      (M : Manifold) →
      TangentBundle M →
      Set

    Curvature :
      (M : Manifold) →
      (TM : TangentBundle M) →
      Connection M TM →
      Set

    interfaceTargetName :
      String

    interfaceTargetName-v :
      interfaceTargetName
      ≡
      "target-only-PhysLean-differential-geometry-core-interface"

    interfacesNamed :
      Bool

    interfacesNamedIsTrue :
      interfacesNamed ≡ true

    concreteAdaptersImported :
      Bool

    concreteAdaptersImportedIsFalse :
      concreteAdaptersImported ≡ false

open CoreDifferentialGeometryInterfaceSurface public

record DifferentialFormCalculusSurface
    (core : CoreDifferentialGeometryInterfaceSurface)
    : Setω where
  field
    ExteriorDerivative :
      (M : Manifold core) →
      DifferentialForm core M →
      DifferentialForm core M

    InteriorProduct :
      (M : Manifold core) →
      VectorField core M →
      DifferentialForm core M →
      DifferentialForm core M

    LieDerivative :
      (M : Manifold core) →
      VectorField core M →
      DifferentialForm core M →
      DifferentialForm core M

    Boundary :
      Manifold core →
      Set

    DeRhamCohomologyClass :
      Manifold core →
      Set

    calculusTargetName :
      String

    calculusTargetName-v :
      calculusTargetName
      ≡
      "target-only-exterior-calculus-d-iX-LX-boundary-deRham"

    calculusAdaptersImported :
      Bool

    calculusAdaptersImportedIsFalse :
      calculusAdaptersImported ≡ false

open DifferentialFormCalculusSurface public

record DifferentialGeometryIdentitySurface
    (core : CoreDifferentialGeometryInterfaceSurface)
    (calculus : DifferentialFormCalculusSurface core)
    : Setω where
  field
    exteriorDerivativeSquaresToZeroNamed :
      Bool

    exteriorDerivativeSquaresToZeroNamedIsTrue :
      exteriorDerivativeSquaresToZeroNamed ≡ true

    exteriorDerivativeSquaresToZeroProved :
      Bool

    exteriorDerivativeSquaresToZeroProvedIsFalse :
      exteriorDerivativeSquaresToZeroProved ≡ false

    cartanFormulaNamed :
      Bool

    cartanFormulaNamedIsTrue :
      cartanFormulaNamed ≡ true

    cartanFormulaProved :
      Bool

    cartanFormulaProvedIsFalse :
      cartanFormulaProved ≡ false

    stokesTheoremNamed :
      Bool

    stokesTheoremNamedIsTrue :
      stokesTheoremNamed ≡ true

    stokesTheoremProved :
      Bool

    stokesTheoremProvedIsFalse :
      stokesTheoremProved ≡ false

    poincareLemmaNamed :
      Bool

    poincareLemmaNamedIsTrue :
      poincareLemmaNamed ≡ true

    poincareLemmaProved :
      Bool

    poincareLemmaProvedIsFalse :
      poincareLemmaProved ≡ false

    bianchiIdentityNamed :
      Bool

    bianchiIdentityNamedIsTrue :
      bianchiIdentityNamed ≡ true

    bianchiIdentityProved :
      Bool

    bianchiIdentityProvedIsFalse :
      bianchiIdentityProved ≡ false

    identityTargetNames :
      List DifferentialGeometryIdentityTarget

    identityTargetNamesAreCanonical :
      identityTargetNames
      ≡
      canonicalDifferentialGeometryIdentityTargets

open DifferentialGeometryIdentitySurface public

record DifferentialGeometryParityReceipt : Setω where
  field
    status :
      DifferentialGeometryParityStatus

    coreInterface :
      CoreDifferentialGeometryInterfaceSurface

    formCalculus :
      DifferentialFormCalculusSurface coreInterface

    identitySurface :
      DifferentialGeometryIdentitySurface coreInterface formCalculus

    coveredConcepts :
      List DifferentialGeometryConcept

    coveredConceptsAreCanonical :
      coveredConcepts
      ≡
      canonicalDifferentialGeometryConcepts

    openObligations :
      List DifferentialGeometryOpenObligation

    openObligationsAreCanonical :
      openObligations
      ≡
      canonicalDifferentialGeometryOpenObligations

    physLeanParityLayerNamed :
      Bool

    physLeanParityLayerNamedIsTrue :
      physLeanParityLayerNamed ≡ true

    physLeanAdaptersImported :
      Bool

    physLeanAdaptersImportedIsFalse :
      physLeanAdaptersImported ≡ false

    identityProofsImported :
      Bool

    identityProofsImportedIsFalse :
      identityProofsImported ≡ false

    parityPromoted :
      Bool

    parityPromotedIsFalse :
      parityPromoted ≡ false

    noPromotionWithoutAuthority :
      DifferentialGeometryParityAuthorityToken →
      ⊥

    receiptBoundary :
      List String

open DifferentialGeometryParityReceipt public

canonicalCoreDifferentialGeometryInterfaceSurface :
  CoreDifferentialGeometryInterfaceSurface
canonicalCoreDifferentialGeometryInterfaceSurface =
  record
    { Manifold =
        ⊥
    ; SmoothMap =
        λ ()
    ; TangentBundle =
        λ ()
    ; CotangentBundle =
        λ ()
    ; DifferentialForm =
        λ ()
    ; VectorField =
        λ ()
    ; Metric =
        λ ()
    ; Connection =
        λ ()
    ; Curvature =
        λ ()
    ; interfaceTargetName =
        "target-only-PhysLean-differential-geometry-core-interface"
    ; interfaceTargetName-v =
        refl
    ; interfacesNamed =
        true
    ; interfacesNamedIsTrue =
        refl
    ; concreteAdaptersImported =
        false
    ; concreteAdaptersImportedIsFalse =
        refl
    }

canonicalDifferentialFormCalculusSurface :
  DifferentialFormCalculusSurface
    canonicalCoreDifferentialGeometryInterfaceSurface
canonicalDifferentialFormCalculusSurface =
  record
    { ExteriorDerivative =
        λ ()
    ; InteriorProduct =
        λ ()
    ; LieDerivative =
        λ ()
    ; Boundary =
        λ ()
    ; DeRhamCohomologyClass =
        λ ()
    ; calculusTargetName =
        "target-only-exterior-calculus-d-iX-LX-boundary-deRham"
    ; calculusTargetName-v =
        refl
    ; calculusAdaptersImported =
        false
    ; calculusAdaptersImportedIsFalse =
        refl
    }

canonicalDifferentialGeometryIdentitySurface :
  DifferentialGeometryIdentitySurface
    canonicalCoreDifferentialGeometryInterfaceSurface
    canonicalDifferentialFormCalculusSurface
canonicalDifferentialGeometryIdentitySurface =
  record
    { exteriorDerivativeSquaresToZeroNamed =
        true
    ; exteriorDerivativeSquaresToZeroNamedIsTrue =
        refl
    ; exteriorDerivativeSquaresToZeroProved =
        false
    ; exteriorDerivativeSquaresToZeroProvedIsFalse =
        refl
    ; cartanFormulaNamed =
        true
    ; cartanFormulaNamedIsTrue =
        refl
    ; cartanFormulaProved =
        false
    ; cartanFormulaProvedIsFalse =
        refl
    ; stokesTheoremNamed =
        true
    ; stokesTheoremNamedIsTrue =
        refl
    ; stokesTheoremProved =
        false
    ; stokesTheoremProvedIsFalse =
        refl
    ; poincareLemmaNamed =
        true
    ; poincareLemmaNamedIsTrue =
        refl
    ; poincareLemmaProved =
        false
    ; poincareLemmaProvedIsFalse =
        refl
    ; bianchiIdentityNamed =
        true
    ; bianchiIdentityNamedIsTrue =
        refl
    ; bianchiIdentityProved =
        false
    ; bianchiIdentityProvedIsFalse =
        refl
    ; identityTargetNames =
        canonicalDifferentialGeometryIdentityTargets
    ; identityTargetNamesAreCanonical =
        refl
    }

canonicalDifferentialGeometryParityReceipt :
  DifferentialGeometryParityReceipt
canonicalDifferentialGeometryParityReceipt =
  record
    { status =
        differentialGeometryTargetsOnlyNoPromotion
    ; coreInterface =
        canonicalCoreDifferentialGeometryInterfaceSurface
    ; formCalculus =
        canonicalDifferentialFormCalculusSurface
    ; identitySurface =
        canonicalDifferentialGeometryIdentitySurface
    ; coveredConcepts =
        canonicalDifferentialGeometryConcepts
    ; coveredConceptsAreCanonical =
        refl
    ; openObligations =
        canonicalDifferentialGeometryOpenObligations
    ; openObligationsAreCanonical =
        refl
    ; physLeanParityLayerNamed =
        true
    ; physLeanParityLayerNamedIsTrue =
        refl
    ; physLeanAdaptersImported =
        false
    ; physLeanAdaptersImportedIsFalse =
        refl
    ; identityProofsImported =
        false
    ; identityProofsImportedIsFalse =
        refl
    ; parityPromoted =
        false
    ; parityPromotedIsFalse =
        refl
    ; noPromotionWithoutAuthority =
        λ ()
    ; receiptBoundary =
        "PhysLean differential-geometry vocabulary is named as a DASHI parity target only"
        ∷ "Manifold, SmoothMap, TangentBundle, CotangentBundle, DifferentialForm, VectorField, Metric, Connection, and Curvature are interface sockets"
        ∷ "d-o-d=0, Cartan, Stokes, Poincare, and Bianchi are named identity targets, not proved theorems"
        ∷ "physLeanAdaptersImported, identityProofsImported, and parityPromoted remain false without external authority"
        ∷ []
    }

differentialGeometryParityPromotedIsFalse :
  parityPromoted canonicalDifferentialGeometryParityReceipt
  ≡
  false
differentialGeometryParityPromotedIsFalse =
  refl

differentialGeometryIdentityProofsImportedIsFalse :
  identityProofsImported canonicalDifferentialGeometryParityReceipt
  ≡
  false
differentialGeometryIdentityProofsImportedIsFalse =
  refl

differentialGeometryOpenObligationsCanonical :
  openObligations canonicalDifferentialGeometryParityReceipt
  ≡
  canonicalDifferentialGeometryOpenObligations
differentialGeometryOpenObligationsCanonical =
  refl
