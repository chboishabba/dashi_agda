module DASHI.Physics.Closure.GeometryAnalogueClassification where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; _∷_; [])
open import Agda.Builtin.String using (String)

import DASHI.Interop.PNFHyperfabric369 as Hyperfabric369
import DASHI.Physics.Closure.BruhatTitsProductTreeReceipt as BT
import DASHI.Physics.Closure.HolographicBulkBoundaryReceipt as Boundary

data ⊥ : Set where

------------------------------------------------------------------------
-- Geometry-analogue classification.
--
-- This module classifies carrier geometries by analogy only.  It records
-- literal Archimedean Thurston geometries as one branch, and keeps
-- non-Archimedean tree, finite hypervoxel, and p-adic boundary placements as
-- different constructors.  The fail-closed flags below prevent this analogue
-- placement from being read as smooth geometry identification or
-- geometrization.

data ThurstonGeometry : Set where
  S3 :
    ThurstonGeometry

  E3 :
    ThurstonGeometry

  H3 :
    ThurstonGeometry

  S2xR :
    ThurstonGeometry

  H2xR :
    ThurstonGeometry

  Nil :
    ThurstonGeometry

  Sol :
    ThurstonGeometry

  SL2R :
    ThurstonGeometry

thurstonGeometryLabel : ThurstonGeometry → String
thurstonGeometryLabel S3 =
  "literal Archimedean S3 Thurston geometry"
thurstonGeometryLabel E3 =
  "literal Archimedean E3 Thurston geometry"
thurstonGeometryLabel H3 =
  "literal Archimedean H3 Thurston geometry"
thurstonGeometryLabel S2xR =
  "literal Archimedean S2 x R Thurston geometry"
thurstonGeometryLabel H2xR =
  "literal Archimedean H2 x R Thurston geometry"
thurstonGeometryLabel Nil =
  "literal Archimedean Nil Thurston geometry"
thurstonGeometryLabel Sol =
  "literal Archimedean Sol Thurston geometry"
thurstonGeometryLabel SL2R =
  "literal Archimedean SL2(R) Thurston geometry"

data GeometryAnalogue : Set where
  literalThurston :
    ThurstonGeometry →
    GeometryAnalogue

  nonArchHypTree :
    GeometryAnalogue

  finiteFlatCell :
    GeometryAnalogue

  pAdicBoundary :
    GeometryAnalogue

geometryAnalogueLabel : GeometryAnalogue → String
geometryAnalogueLabel (literalThurston geometry) =
  thurstonGeometryLabel geometry
geometryAnalogueLabel nonArchHypTree =
  "non-Archimedean hyperbolic-tree analogue"
geometryAnalogueLabel finiteFlatCell =
  "finite flat-cell hypervoxel analogue"
geometryAnalogueLabel pAdicBoundary =
  "p-adic ultrametric boundary analogue"

_≢_ : {A : Set} → A → A → Set
x ≢ y =
  x ≡ y → ⊥

notTrue : Bool → Set
notTrue flag =
  flag ≡ true → ⊥

falseNotTrue : notTrue false
falseNotTrue ()

nonArchHypTreeNotLiteralH3 :
  nonArchHypTree ≢ literalThurston H3
nonArchHypTreeNotLiteralH3 ()

finiteFlatCellNotLiteralE3 :
  finiteFlatCell ≢ literalThurston E3
finiteFlatCellNotLiteralE3 ()

pAdicBoundaryNotLiteralH3 :
  pAdicBoundary ≢ literalThurston H3
pAdicBoundaryNotLiteralH3 ()

pAdicBoundaryNotLiteralE3 :
  pAdicBoundary ≢ literalThurston E3
pAdicBoundaryNotLiteralE3 ()

------------------------------------------------------------------------
-- Evidence tags reused from the receipts where possible.

data GeometryEvidenceTag : Set where
  productTreeFact :
    BT.ProductTreeGeometryFact →
    GeometryEvidenceTag

  productTreeSpatialCarrier :
    BT.ProductTreeSpatialCarrier →
    GeometryEvidenceTag

  productTreeContinuumCarrier :
    BT.PAdicContinuumCarrier →
    GeometryEvidenceTag

  hyperfabricObject :
    Hyperfabric369.HyperfabricObject →
    GeometryEvidenceTag

  hyperfabricAxis :
    Hyperfabric369.EncodingAxis →
    GeometryEvidenceTag

  boundaryTreeFactor :
    Boundary.CarrierTreeFactor →
    GeometryEvidenceTag

  boundaryFactor :
    Boundary.CarrierBoundaryFactor →
    GeometryEvidenceTag

  pAdicHolographyAuthority :
    Boundary.PAdicHolographyAuthority →
    GeometryEvidenceTag

canonicalBTProductTreeEvidenceTags : List GeometryEvidenceTag
canonicalBTProductTreeEvidenceTags =
  productTreeSpatialCarrier
    (BT.spatialCarrier BT.canonicalBruhatTitsProductTreeReceipt)
  ∷ productTreeFact BT.T3DeltaZeroGromovHyperbolic
  ∷ productTreeFact BT.T2DeltaZeroGromovHyperbolic
  ∷ productTreeFact BT.T7DeltaZeroGromovHyperbolic
  ∷ productTreeContinuumCarrier
    (BT.continuumCarrier BT.canonicalBruhatTitsProductTreeReceipt)
  ∷ []

canonicalHypervoxel369EvidenceTags : List GeometryEvidenceTag
canonicalHypervoxel369EvidenceTags =
  hyperfabricObject Hyperfabric369.dialecticDiscussionAtom27
  ∷ hyperfabricObject Hyperfabric369.documentTimeHypervoxel
  ∷ hyperfabricObject Hyperfabric369.pAdicDecimalValuationFabric
  ∷ hyperfabricAxis Hyperfabric369.documentTimeAxis
  ∷ []

canonicalBTBoundaryEvidenceTags : List GeometryEvidenceTag
canonicalBTBoundaryEvidenceTags =
  boundaryTreeFactor Boundary.T3
  ∷ boundaryTreeFactor Boundary.T2
  ∷ boundaryTreeFactor Boundary.T7
  ∷ boundaryFactor Boundary.P1Q3
  ∷ boundaryFactor Boundary.P1Q2
  ∷ boundaryFactor Boundary.P1Q7
  ∷ pAdicHolographyAuthority
    (Boundary.pAdicAdSCFTAuthority
      Boundary.canonicalHolographicBulkBoundaryReceipt)
  ∷ []

------------------------------------------------------------------------
-- Concrete placements.

BTProductTreeGeometry : GeometryAnalogue
BTProductTreeGeometry =
  nonArchHypTree

Hypervoxel369Geometry : GeometryAnalogue
Hypervoxel369Geometry =
  finiteFlatCell

BTBoundaryGeometry : GeometryAnalogue
BTBoundaryGeometry =
  pAdicBoundary

BTProductTreeGeometryIsNonArchHypTree :
  BTProductTreeGeometry ≡ nonArchHypTree
BTProductTreeGeometryIsNonArchHypTree =
  refl

Hypervoxel369GeometryIsFiniteFlatCell :
  Hypervoxel369Geometry ≡ finiteFlatCell
Hypervoxel369GeometryIsFiniteFlatCell =
  refl

BTBoundaryGeometryIspAdicBoundary :
  BTBoundaryGeometry ≡ pAdicBoundary
BTBoundaryGeometryIspAdicBoundary =
  refl

record GeometryAnalogueAssignment : Set where
  field
    geometry :
      GeometryAnalogue

    geometryLabel :
      String

    geometryLabelIsCanonical :
      geometryLabel ≡ geometryAnalogueLabel geometry

    evidenceTags :
      List GeometryEvidenceTag

    smoothGeometryIdentified :
      Bool

    smoothGeometryIdentifiedIsFalse :
      smoothGeometryIdentified ≡ false

    smoothGeometryIdentificationBlocked :
      notTrue smoothGeometryIdentified

    geometrizationPromoted :
      Bool

    geometrizationPromotedIsFalse :
      geometrizationPromoted ≡ false

    geometrizationPromotionBlocked :
      notTrue geometrizationPromoted

open GeometryAnalogueAssignment public

record BTProductTreeGeometryAssignment : Setω where
  field
    receipt :
      BT.BruhatTitsProductTreeReceipt

    receiptSpatialCarrierIsCanonical :
      BT.spatialCarrier receipt ≡ BT.T3xT2xT7Carrier

    receiptContinuumCarrierIsCanonical :
      BT.continuumCarrier receipt ≡ BT.Q3xQ2xQ7Continuum

    assignment :
      GeometryAnalogueAssignment

    geometryIsNonArchHypTree :
      geometry assignment ≡ nonArchHypTree

    notLiteralH3 :
      geometry assignment ≢ literalThurston H3

    notLiteralE3 :
      geometry assignment ≢ literalThurston E3

open BTProductTreeGeometryAssignment public

canonicalBTProductTreeGeometryAssignment :
  BTProductTreeGeometryAssignment
canonicalBTProductTreeGeometryAssignment =
  record
    { receipt =
        BT.canonicalBruhatTitsProductTreeReceipt
    ; receiptSpatialCarrierIsCanonical =
        refl
    ; receiptContinuumCarrierIsCanonical =
        refl
    ; assignment =
        record
          { geometry =
              BTProductTreeGeometry
          ; geometryLabel =
              geometryAnalogueLabel BTProductTreeGeometry
          ; geometryLabelIsCanonical =
              refl
          ; evidenceTags =
              canonicalBTProductTreeEvidenceTags
          ; smoothGeometryIdentified =
              false
          ; smoothGeometryIdentifiedIsFalse =
              refl
          ; smoothGeometryIdentificationBlocked =
              falseNotTrue
          ; geometrizationPromoted =
              false
          ; geometrizationPromotedIsFalse =
              refl
          ; geometrizationPromotionBlocked =
              falseNotTrue
          }
    ; geometryIsNonArchHypTree =
        refl
    ; notLiteralH3 =
        nonArchHypTreeNotLiteralH3
    ; notLiteralE3 =
        λ ()
    }

record Hypervoxel369GeometryAssignment : Set₁ where
  field
    surface :
      Hyperfabric369.PNFHyperfabric369Surface

    surfaceIsCanonical :
      surface ≡ Hyperfabric369.canonicalPNFHyperfabric369Surface

    assignment :
      GeometryAnalogueAssignment

    geometryIsFiniteFlatCell :
      geometry assignment ≡ finiteFlatCell

    notLiteralH3 :
      geometry assignment ≢ literalThurston H3

    notLiteralE3 :
      geometry assignment ≢ literalThurston E3

open Hypervoxel369GeometryAssignment public

canonicalHypervoxel369GeometryAssignment :
  Hypervoxel369GeometryAssignment
canonicalHypervoxel369GeometryAssignment =
  record
    { surface =
        Hyperfabric369.canonicalPNFHyperfabric369Surface
    ; surfaceIsCanonical =
        refl
    ; assignment =
        record
          { geometry =
              Hypervoxel369Geometry
          ; geometryLabel =
              geometryAnalogueLabel Hypervoxel369Geometry
          ; geometryLabelIsCanonical =
              refl
          ; evidenceTags =
              canonicalHypervoxel369EvidenceTags
          ; smoothGeometryIdentified =
              false
          ; smoothGeometryIdentifiedIsFalse =
              refl
          ; smoothGeometryIdentificationBlocked =
              falseNotTrue
          ; geometrizationPromoted =
              false
          ; geometrizationPromotedIsFalse =
              refl
          ; geometrizationPromotionBlocked =
              falseNotTrue
          }
    ; geometryIsFiniteFlatCell =
        refl
    ; notLiteralH3 =
        λ ()
    ; notLiteralE3 =
        finiteFlatCellNotLiteralE3
    }

record BTBoundaryGeometryAssignment : Setω where
  field
    receipt :
      Boundary.HolographicBulkBoundaryReceipt

    receiptBoundaryFactorsAreCanonical :
      Boundary.carrierBoundaryFactors receipt
      ≡
      Boundary.canonicalCarrierBoundaryFactors

    receiptBoundaryProductIsCanonical :
      Boundary.carrierBoundaryProduct receipt
      ≡
      "P^1(Q_3) x P^1(Q_2) x P^1(Q_7)"

    assignment :
      GeometryAnalogueAssignment

    geometryIspAdicBoundary :
      geometry assignment ≡ pAdicBoundary

    notLiteralH3 :
      geometry assignment ≢ literalThurston H3

    notLiteralE3 :
      geometry assignment ≢ literalThurston E3

open BTBoundaryGeometryAssignment public

canonicalBTBoundaryGeometryAssignment :
  BTBoundaryGeometryAssignment
canonicalBTBoundaryGeometryAssignment =
  record
    { receipt =
        Boundary.canonicalHolographicBulkBoundaryReceipt
    ; receiptBoundaryFactorsAreCanonical =
        refl
    ; receiptBoundaryProductIsCanonical =
        refl
    ; assignment =
        record
          { geometry =
              BTBoundaryGeometry
          ; geometryLabel =
              geometryAnalogueLabel BTBoundaryGeometry
          ; geometryLabelIsCanonical =
              refl
          ; evidenceTags =
              canonicalBTBoundaryEvidenceTags
          ; smoothGeometryIdentified =
              false
          ; smoothGeometryIdentifiedIsFalse =
              refl
          ; smoothGeometryIdentificationBlocked =
              falseNotTrue
          ; geometrizationPromoted =
              false
          ; geometrizationPromotedIsFalse =
              refl
          ; geometrizationPromotionBlocked =
              falseNotTrue
          }
    ; geometryIspAdicBoundary =
        refl
    ; notLiteralH3 =
        pAdicBoundaryNotLiteralH3
    ; notLiteralE3 =
        pAdicBoundaryNotLiteralE3
    }

------------------------------------------------------------------------
-- Classification surface and explicit fail-closed checks.

record GeometryAnalogueClassification : Setω where
  field
    btProductTree :
      BTProductTreeGeometryAssignment

    hypervoxel369 :
      Hypervoxel369GeometryAssignment

    btBoundary :
      BTBoundaryGeometryAssignment

    smoothGeometryIdentificationPromoted :
      Bool

    smoothGeometryIdentificationPromotedIsFalse :
      smoothGeometryIdentificationPromoted ≡ false

    smoothGeometryIdentificationBlocked :
      notTrue smoothGeometryIdentificationPromoted

    geometrizationPromoted :
      Bool

    geometrizationPromotedIsFalse :
      geometrizationPromoted ≡ false

    geometrizationBlocked :
      notTrue geometrizationPromoted

    classificationBoundary :
      List String

open GeometryAnalogueClassification public

canonicalGeometryAnalogueClassification :
  GeometryAnalogueClassification
canonicalGeometryAnalogueClassification =
  record
    { btProductTree =
        canonicalBTProductTreeGeometryAssignment
    ; hypervoxel369 =
        canonicalHypervoxel369GeometryAssignment
    ; btBoundary =
        canonicalBTBoundaryGeometryAssignment
    ; smoothGeometryIdentificationPromoted =
        false
    ; smoothGeometryIdentificationPromotedIsFalse =
        refl
    ; smoothGeometryIdentificationBlocked =
        falseNotTrue
    ; geometrizationPromoted =
        false
    ; geometrizationPromotedIsFalse =
        refl
    ; geometrizationBlocked =
        falseNotTrue
    ; classificationBoundary =
        "BT product tree is classified as a non-Archimedean hyperbolic-tree analogue, not literal H3."
        ∷ "369 document-time hypervoxel is classified as a finite flat-cell analogue, not literal E3."
        ∷ "BT boundary is classified as a p-adic ultrametric boundary analogue, not literal H3 or E3."
        ∷ "Smooth geometry identification and geometrization remain fail-closed."
        ∷ []
    }

classificationBTProductTreeNonArch :
  geometry
    (assignment
      (btProductTree canonicalGeometryAnalogueClassification))
  ≡
  nonArchHypTree
classificationBTProductTreeNonArch =
  refl

classificationHypervoxel369FiniteFlat :
  geometry
    (assignment
      (hypervoxel369 canonicalGeometryAnalogueClassification))
  ≡
  finiteFlatCell
classificationHypervoxel369FiniteFlat =
  refl

classificationBTBoundaryPAdic :
  geometry
    (assignment
      (btBoundary canonicalGeometryAnalogueClassification))
  ≡
  pAdicBoundary
classificationBTBoundaryPAdic =
  refl

classificationSmoothGeometryIdentificationBlocked :
  notTrue
    (smoothGeometryIdentificationPromoted
      canonicalGeometryAnalogueClassification)
classificationSmoothGeometryIdentificationBlocked =
  falseNotTrue

classificationGeometrizationBlocked :
  notTrue (geometrizationPromoted canonicalGeometryAnalogueClassification)
classificationGeometrizationBlocked =
  falseNotTrue
