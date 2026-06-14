module DASHI.Physics.Closure.GeometryJSJAnalogueCrosswalk where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; _∷_; [])
open import Agda.Builtin.String using (String)

import DASHI.Physics.Closure.GeometryAnalogueClassification as Geometry
import DASHI.Physics.Closure.JSJAnaloguePieceClassification as JSJ

------------------------------------------------------------------------
-- Geometry/JSJ analogue crosswalk.
--
-- This module is a typed matrix between the geometry-analogue ledger and the
-- JSJ-analogue piece ledger.  It records only crosswalk rows: no smooth H3/E3
-- identification, no literal JSJ theorem, and no aggregator wiring.

record GeometryJSJAnalogueCrosswalkRow : Set where
  constructor geometryJSJAnalogueCrosswalkRow
  field
    analoguePiece :
      JSJ.AnaloguePiece

    geometryAnalogue :
      Geometry.GeometryAnalogue

    boundaryKind :
      JSJ.BoundaryKind

    blockers :
      List JSJ.DecompositionBlocker

    pieceBoundaryMatches :
      JSJ.boundary analoguePiece ≡ boundaryKind

    pieceBlockersMatch :
      JSJ.blockers analoguePiece ≡ blockers

    notLiteralH3 :
      geometryAnalogue Geometry.≢ Geometry.literalThurston Geometry.H3

    notLiteralE3 :
      geometryAnalogue Geometry.≢ Geometry.literalThurston Geometry.E3

    literalH3Identification :
      Bool

    literalH3IdentificationIsFalse :
      literalH3Identification ≡ false

    literalH3IdentificationBlocked :
      Geometry.notTrue literalH3Identification

    literalE3Identification :
      Bool

    literalE3IdentificationIsFalse :
      literalE3Identification ≡ false

    literalE3IdentificationBlocked :
      Geometry.notTrue literalE3Identification

    jsjTheoremAvailable :
      Bool

    jsjTheoremAvailableIsFalse :
      jsjTheoremAvailable ≡ false

    jsjTheoremAvailability :
      JSJ.TheoremAvailability

    jsjTheoremAvailabilityUnavailable :
      jsjTheoremAvailability ≡ JSJ.theoremUnavailableHere

open GeometryJSJAnalogueCrosswalkRow public

btCrosswalkBlockers : List JSJ.DecompositionBlocker
btCrosswalkBlockers =
  JSJ.noIncompressibleTorus
  ∷ JSJ.noPrimeDecomposition
  ∷ JSJ.noJSJUniqueness
  ∷ JSJ.noThurstonGeometrizationTheorem
  ∷ JSJ.noSmoothThreeManifoldCarrier
  ∷ JSJ.nonArchimedeanBoundaryMismatch
  ∷ []

hyperfabric369CrosswalkBlockers : List JSJ.DecompositionBlocker
hyperfabric369CrosswalkBlockers =
  JSJ.noIncompressibleTorus
  ∷ JSJ.noPrimeDecomposition
  ∷ JSJ.noJSJUniqueness
  ∷ JSJ.noThurstonGeometrizationTheorem
  ∷ JSJ.noSmoothThreeManifoldCarrier
  ∷ JSJ.finiteHypercubeOnly
  ∷ []

btGeometryJSJCrosswalkRow : GeometryJSJAnalogueCrosswalkRow
btGeometryJSJCrosswalkRow =
  geometryJSJAnalogueCrosswalkRow
    JSJ.btAtoroidalLikePiece
    Geometry.nonArchHypTree
    JSJ.pAdicProjectiveLineProductBoundary
    btCrosswalkBlockers
    refl
    refl
    Geometry.nonArchHypTreeNotLiteralH3
    (λ ())
    false
    refl
    Geometry.falseNotTrue
    false
    refl
    Geometry.falseNotTrue
    false
    refl
    JSJ.theoremUnavailableHere
    refl

hyperfabric369GeometryJSJCrosswalkRow :
  GeometryJSJAnalogueCrosswalkRow
hyperfabric369GeometryJSJCrosswalkRow =
  geometryJSJAnalogueCrosswalkRow
    JSJ.hyperfabric369FiniteFlatTorusLikePiece
    Geometry.finiteFlatCell
    JSJ.finiteHyperfabricTorusLikeBoundary
    hyperfabric369CrosswalkBlockers
    refl
    refl
    (λ ())
    Geometry.finiteFlatCellNotLiteralE3
    false
    refl
    Geometry.falseNotTrue
    false
    refl
    Geometry.falseNotTrue
    false
    refl
    JSJ.theoremUnavailableHere
    refl

canonicalGeometryJSJAnalogueCrosswalkRows :
  List GeometryJSJAnalogueCrosswalkRow
canonicalGeometryJSJAnalogueCrosswalkRows =
  btGeometryJSJCrosswalkRow
  ∷ hyperfabric369GeometryJSJCrosswalkRow
  ∷ []

btCrosswalkGeometryIsNonArchHypTree :
  geometryAnalogue btGeometryJSJCrosswalkRow
  ≡
  Geometry.nonArchHypTree
btCrosswalkGeometryIsNonArchHypTree =
  refl

btCrosswalkBoundaryIsPAdicProduct :
  boundaryKind btGeometryJSJCrosswalkRow
  ≡
  JSJ.pAdicProjectiveLineProductBoundary
btCrosswalkBoundaryIsPAdicProduct =
  refl

hyperfabric369CrosswalkGeometryIsFiniteFlatCell :
  geometryAnalogue hyperfabric369GeometryJSJCrosswalkRow
  ≡
  Geometry.finiteFlatCell
hyperfabric369CrosswalkGeometryIsFiniteFlatCell =
  refl

hyperfabric369CrosswalkBoundaryIsFiniteTorusLike :
  boundaryKind hyperfabric369GeometryJSJCrosswalkRow
  ≡
  JSJ.finiteHyperfabricTorusLikeBoundary
hyperfabric369CrosswalkBoundaryIsFiniteTorusLike =
  refl

literalH3IdentificationAvailable : Bool
literalH3IdentificationAvailable =
  false

literalE3IdentificationAvailable : Bool
literalE3IdentificationAvailable =
  false

jsjTheoremAvailableHere : Bool
jsjTheoremAvailableHere =
  false

literalH3IdentificationAvailableIsFalse :
  literalH3IdentificationAvailable ≡ false
literalH3IdentificationAvailableIsFalse =
  refl

literalE3IdentificationAvailableIsFalse :
  literalE3IdentificationAvailable ≡ false
literalE3IdentificationAvailableIsFalse =
  refl

jsjTheoremAvailableHereIsFalse :
  jsjTheoremAvailableHere ≡ false
jsjTheoremAvailableHereIsFalse =
  refl

jsjTheoremAvailabilityStatus : JSJ.TheoremAvailability
jsjTheoremAvailabilityStatus =
  JSJ.theoremUnavailableHere

jsjTheoremAvailabilityStatusUnavailable :
  jsjTheoremAvailabilityStatus ≡ JSJ.theoremUnavailableHere
jsjTheoremAvailabilityStatusUnavailable =
  refl

record GeometryJSJAnalogueCrosswalkMatrix : Setω where
  constructor geometryJSJAnalogueCrosswalkMatrix
  field
    geometryClassification :
      Geometry.GeometryAnalogueClassification

    jsjPieceClassification :
      JSJ.JSJAnaloguePieceClassificationReceipt

    rows :
      List GeometryJSJAnalogueCrosswalkRow

    rowsAreCanonical :
      rows ≡ canonicalGeometryJSJAnalogueCrosswalkRows

    btRow :
      GeometryJSJAnalogueCrosswalkRow

    btRowIsCanonical :
      btRow ≡ btGeometryJSJCrosswalkRow

    btRowGeometryField :
      geometryAnalogue btRow ≡ Geometry.nonArchHypTree

    btRowBoundaryField :
      boundaryKind btRow ≡ JSJ.pAdicProjectiveLineProductBoundary

    hyperfabric369Row :
      GeometryJSJAnalogueCrosswalkRow

    hyperfabric369RowIsCanonical :
      hyperfabric369Row ≡ hyperfabric369GeometryJSJCrosswalkRow

    hyperfabric369RowGeometryField :
      geometryAnalogue hyperfabric369Row ≡ Geometry.finiteFlatCell

    hyperfabric369RowBoundaryField :
      boundaryKind hyperfabric369Row
      ≡
      JSJ.finiteHyperfabricTorusLikeBoundary

    literalH3IdentificationFalseField :
      literalH3IdentificationAvailable ≡ false

    literalE3IdentificationFalseField :
      literalE3IdentificationAvailable ≡ false

    jsjTheoremAvailableFalseField :
      jsjTheoremAvailableHere ≡ false

    jsjTheoremUnavailableField :
      jsjTheoremAvailabilityStatus ≡ JSJ.theoremUnavailableHere

open GeometryJSJAnalogueCrosswalkMatrix public

canonicalGeometryJSJAnalogueCrosswalkMatrix :
  GeometryJSJAnalogueCrosswalkMatrix
canonicalGeometryJSJAnalogueCrosswalkMatrix =
  geometryJSJAnalogueCrosswalkMatrix
    Geometry.canonicalGeometryAnalogueClassification
    JSJ.canonicalJSJAnaloguePieceClassificationReceipt
    canonicalGeometryJSJAnalogueCrosswalkRows
    refl
    btGeometryJSJCrosswalkRow
    refl
    refl
    refl
    hyperfabric369GeometryJSJCrosswalkRow
    refl
    refl
    refl
    refl
    refl
    refl
    refl

organizationString : String
organizationString =
  "O: Geometry/JSJ analogue crosswalk records typed matrix rows for BT and 369."

requirementString : String
requirementString =
  "R: Link each JSJ analogue piece to a geometry analogue, boundary kind, blockers, and fail-closed theorem status."

codeArtifactString : String
codeArtifactString =
  "C: GeometryJSJAnalogueCrosswalk imports both classifications and exports crosswalk row and matrix records."

stateString : String
stateString =
  "S: BT maps to nonArchHypTree with pAdicProjectiveLineProductBoundary; 369 maps to finiteFlatCell with finiteHyperfabricTorusLikeBoundary."

latticeString : String
latticeString =
  "L: analogue piece -> geometry analogue -> boundary kind -> blocker list -> false literal H3/E3 and unavailable JSJ theorem fields."

proposalString : String
proposalString =
  "P: Use the matrix as bookkeeping only; do not promote it to smooth H3/E3 identification or JSJ theorem availability."

governanceString : String
governanceString =
  "G: Fail-closed witnesses keep literal geometry identification false and theorem availability unavailable."

gapString : String
gapString =
  "F: Missing evidence remains a smooth 3-manifold carrier plus JSJ theorem transfer data."

record GeometryJSJAnalogueCrosswalkORCSLPGF : Set where
  constructor geometryJSJAnalogueCrosswalkORCSLPGF
  field
    O : String
    OIsCanonical : O ≡ organizationString
    R : String
    RIsCanonical : R ≡ requirementString
    C : String
    CIsCanonical : C ≡ codeArtifactString
    S : String
    SIsCanonical : S ≡ stateString
    L : String
    LIsCanonical : L ≡ latticeString
    P : String
    PIsCanonical : P ≡ proposalString
    G : String
    GIsCanonical : G ≡ governanceString
    F : String
    FIsCanonical : F ≡ gapString

open GeometryJSJAnalogueCrosswalkORCSLPGF public

canonicalGeometryJSJAnalogueCrosswalkORCSLPGF :
  GeometryJSJAnalogueCrosswalkORCSLPGF
canonicalGeometryJSJAnalogueCrosswalkORCSLPGF =
  geometryJSJAnalogueCrosswalkORCSLPGF
    organizationString
    refl
    requirementString
    refl
    codeArtifactString
    refl
    stateString
    refl
    latticeString
    refl
    proposalString
    refl
    governanceString
    refl
    gapString
    refl
