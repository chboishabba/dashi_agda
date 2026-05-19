module DASHI.Geometry.CharacteristicClassReceiptSurface where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- Characteristic-class receipt surface.
--
-- This module is a non-promoting downstream receipt for characteristic-class
-- targets.  It records typed sockets for AHSS obstruction classification
-- [C,BG], Chern-Weil maps, Pontryagin/Euler class targets, and the dependency
-- boundary on B0 plus a Levi-Civita/torsion-free metric-compatible adapter.
-- It does not import DCHoTT, construct a G-structure, construct a
-- Levi-Civita connection, or prove any characteristic-class theorem.

data CharacteristicClassSurfaceStatus : Set where
  characteristicClassTargetsOnlyNoPromotion :
    CharacteristicClassSurfaceStatus

data CharacteristicClassOpenObligation : Set where
  missingB0GeometricEmergence :
    CharacteristicClassOpenObligation

  missingTorsionFreeLeviCivitaAdapter :
    CharacteristicClassOpenObligation

  missingPrincipalGStructureBundle :
    CharacteristicClassOpenObligation

  missingClassifyingMapToBG :
    CharacteristicClassOpenObligation

  missingAHSSObstructionClassifier :
    CharacteristicClassOpenObligation

  missingChernWeilInvariantPolynomialMap :
    CharacteristicClassOpenObligation

  missingCurvatureFormForChernWeil :
    CharacteristicClassOpenObligation

  missingPontryaginClassTarget :
    CharacteristicClassOpenObligation

  missingEulerClassTarget :
    CharacteristicClassOpenObligation

  missingNaturalityAndGaugeInvariance :
    CharacteristicClassOpenObligation

canonicalCharacteristicClassOpenObligations :
  List CharacteristicClassOpenObligation
canonicalCharacteristicClassOpenObligations =
  missingB0GeometricEmergence
  ∷ missingTorsionFreeLeviCivitaAdapter
  ∷ missingPrincipalGStructureBundle
  ∷ missingClassifyingMapToBG
  ∷ missingAHSSObstructionClassifier
  ∷ missingChernWeilInvariantPolynomialMap
  ∷ missingCurvatureFormForChernWeil
  ∷ missingPontryaginClassTarget
  ∷ missingEulerClassTarget
  ∷ missingNaturalityAndGaugeInvariance
  ∷ []

-- Constructorless: no promotion authority is manufactured here.
data CharacteristicClassPromotionAuthorityToken : Set where

record AHSSObstructionClassificationSurface : Setω where
  field
    CohesiveBase :
      Set

    StructureGroup :
      Set

    ClassifyingSpaceBG :
      StructureGroup →
      Set

    MapToBG :
      CohesiveBase →
      (G : StructureGroup) →
      ClassifyingSpaceBG G →
      Set

    ObstructionPage :
      Set

    ObstructionClass :
      Set

    obstructionClassifier :
      ObstructionPage →
      ObstructionClass

    classificationTargetName :
      String

    classificationTargetName-v :
      classificationTargetName
      ≡
      "target-only-AHSS-obstruction-classification-[C,BG]"

    classifyingMapPromoted :
      Bool

    classifyingMapPromotedIsFalse :
      classifyingMapPromoted ≡ false

open AHSSObstructionClassificationSurface public

record ChernWeilMapSurface : Setω where
  field
    PrincipalBundle :
      Set

    Connection :
      PrincipalBundle →
      Set

    CurvatureForm :
      (P : PrincipalBundle) →
      Connection P →
      Set

    InvariantPolynomial :
      Set

    DeRhamCohomologyClass :
      Set

    chernWeilMap :
      InvariantPolynomial →
      DeRhamCohomologyClass

    chernWeilMapTarget :
      String

    chernWeilMapTarget-v :
      chernWeilMapTarget
      ≡
      "target-only-Chern-Weil-map-from-invariant-polynomials-to-de-Rham-classes"

    curvatureInputConstructed :
      Bool

    curvatureInputConstructedIsFalse :
      curvatureInputConstructed ≡ false

    cWPromoted :
      Bool

    cWPromotedIsFalse :
      cWPromoted ≡ false

open ChernWeilMapSurface public

record PontryaginEulerClassTargetSurface : Setω where
  field
    VectorBundle :
      Set

    OrientedVectorBundle :
      Set

    CohomologyClass :
      Set

    pontryaginClassTarget :
      VectorBundle →
      CohomologyClass

    eulerClassTarget :
      OrientedVectorBundle →
      CohomologyClass

    pontryaginTargetName :
      String

    pontryaginTargetName-v :
      pontryaginTargetName
      ≡
      "target-only-Pontryagin-class-from-Chern-Weil-or-classifying-map"

    eulerTargetName :
      String

    eulerTargetName-v :
      eulerTargetName
      ≡
      "target-only-Euler-class-for-oriented-real-bundle"

    characteristicClassesPromoted :
      Bool

    characteristicClassesPromotedIsFalse :
      characteristicClassesPromoted ≡ false

open PontryaginEulerClassTargetSurface public

record CharacteristicClassReceiptSurface : Setω where
  field
    status :
      CharacteristicClassSurfaceStatus

    ahssSurface :
      AHSSObstructionClassificationSurface

    chernWeilSurface :
      ChernWeilMapSurface

    pontryaginEulerSurface :
      PontryaginEulerClassTargetSurface

    openObligations :
      List CharacteristicClassOpenObligation

    openObligationsAreCanonical :
      openObligations
      ≡
      canonicalCharacteristicClassOpenObligations

    downstreamOfB0 :
      Bool

    downstreamOfB0IsTrue :
      downstreamOfB0 ≡ true

    downstreamOfLeviCivita :
      Bool

    downstreamOfLeviCivitaIsTrue :
      downstreamOfLeviCivita ≡ true

    b0ImportedOrProvedHere :
      Bool

    b0ImportedOrProvedHereIsFalse :
      b0ImportedOrProvedHere ≡ false

    leviCivitaImportedOrProvedHere :
      Bool

    leviCivitaImportedOrProvedHereIsFalse :
      leviCivitaImportedOrProvedHere ≡ false

    promoted :
      Bool

    promotedIsFalse :
      promoted ≡ false

    noPromotionWithoutAuthority :
      CharacteristicClassPromotionAuthorityToken →
      ⊥

    receiptBoundary :
      List String

open CharacteristicClassReceiptSurface public

canonicalAHSSObstructionClassificationSurface :
  AHSSObstructionClassificationSurface
canonicalAHSSObstructionClassificationSurface =
  record
    { CohesiveBase =
        ⊥
    ; StructureGroup =
        ⊥
    ; ClassifyingSpaceBG =
        λ ()
    ; MapToBG =
        λ ()
    ; ObstructionPage =
        ⊥
    ; ObstructionClass =
        ⊥
    ; obstructionClassifier =
        λ ()
    ; classificationTargetName =
        "target-only-AHSS-obstruction-classification-[C,BG]"
    ; classificationTargetName-v =
        refl
    ; classifyingMapPromoted =
        false
    ; classifyingMapPromotedIsFalse =
        refl
    }

canonicalChernWeilMapSurface :
  ChernWeilMapSurface
canonicalChernWeilMapSurface =
  record
    { PrincipalBundle =
        ⊥
    ; Connection =
        λ ()
    ; CurvatureForm =
        λ ()
    ; InvariantPolynomial =
        ⊥
    ; DeRhamCohomologyClass =
        ⊥
    ; chernWeilMap =
        λ ()
    ; chernWeilMapTarget =
        "target-only-Chern-Weil-map-from-invariant-polynomials-to-de-Rham-classes"
    ; chernWeilMapTarget-v =
        refl
    ; curvatureInputConstructed =
        false
    ; curvatureInputConstructedIsFalse =
        refl
    ; cWPromoted =
        false
    ; cWPromotedIsFalse =
        refl
    }

canonicalPontryaginEulerClassTargetSurface :
  PontryaginEulerClassTargetSurface
canonicalPontryaginEulerClassTargetSurface =
  record
    { VectorBundle =
        ⊥
    ; OrientedVectorBundle =
        ⊥
    ; CohomologyClass =
        ⊥
    ; pontryaginClassTarget =
        λ ()
    ; eulerClassTarget =
        λ ()
    ; pontryaginTargetName =
        "target-only-Pontryagin-class-from-Chern-Weil-or-classifying-map"
    ; pontryaginTargetName-v =
        refl
    ; eulerTargetName =
        "target-only-Euler-class-for-oriented-real-bundle"
    ; eulerTargetName-v =
        refl
    ; characteristicClassesPromoted =
        false
    ; characteristicClassesPromotedIsFalse =
        refl
    }

canonicalCharacteristicClassReceiptSurface :
  CharacteristicClassReceiptSurface
canonicalCharacteristicClassReceiptSurface =
  record
    { status =
        characteristicClassTargetsOnlyNoPromotion
    ; ahssSurface =
        canonicalAHSSObstructionClassificationSurface
    ; chernWeilSurface =
        canonicalChernWeilMapSurface
    ; pontryaginEulerSurface =
        canonicalPontryaginEulerClassTargetSurface
    ; openObligations =
        canonicalCharacteristicClassOpenObligations
    ; openObligationsAreCanonical =
        refl
    ; downstreamOfB0 =
        true
    ; downstreamOfB0IsTrue =
        refl
    ; downstreamOfLeviCivita =
        true
    ; downstreamOfLeviCivitaIsTrue =
        refl
    ; b0ImportedOrProvedHere =
        false
    ; b0ImportedOrProvedHereIsFalse =
        refl
    ; leviCivitaImportedOrProvedHere =
        false
    ; leviCivitaImportedOrProvedHereIsFalse =
        refl
    ; promoted =
        false
    ; promotedIsFalse =
        refl
    ; noPromotionWithoutAuthority =
        λ ()
    ; receiptBoundary =
        "Characteristic-class layer is downstream of B0 geometric emergence and a Levi-Civita/torsion-free metric-compatible adapter"
        ∷ "AHSS obstruction classification [C,BG] is recorded only as a target socket"
        ∷ "Chern-Weil map is recorded only as a target from invariant polynomials to de Rham cohomology classes"
        ∷ "Pontryagin and Euler classes are target sockets, not constructed characteristic classes"
        ∷ "No principal G-bundle, classifying map, curvature form, invariant-polynomial theorem, naturality proof, or gauge-invariance proof is constructed here"
        ∷ "This receipt is non-promoting and cannot promote without an external authority token"
        ∷ []
    }

