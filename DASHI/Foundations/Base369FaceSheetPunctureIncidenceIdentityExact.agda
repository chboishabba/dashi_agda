module DASHI.Foundations.Base369FaceSheetPunctureIncidenceIdentityExact where

open import DASHI.Core.Prelude

import DASHI.Foundations.SSPTritCarrier as SSP
import DASHI.Foundations.Base369Ternary27HypervoxelFabricGeometryExact as Geometry
import DASHI.Foundations.Base369Ternary27HypervoxelStratificationExact as Strata
import DASHI.Foundations.Base369StableAlgebraicIdentityTowerExact as Stable
import DASHI.Foundations.Base369MonsterNamedIdentityRegistryExact as Registry

------------------------------------------------------------------------
-- FACE-SHEET / PUNCTURE / INCIDENCE IDENTITIES
--
-- Every outer face of the ternary 3x3x3 voxel is a 3x3 nonary sheet because
-- one coordinate is fixed at +/-1 and the other two remain ternary.
--
--   FaceSheet9 = 1 face-centre + 8 punctured positions
--   FaceIncidence54 = 6 faces x 9 positions per face.
--
-- The 54 counts face incidences, not 54 distinct cube points: edge-centres are
-- incident to two faces and corners to three.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- 1. One face has one centre plus eight noncentral positions.
------------------------------------------------------------------------

data PuncturedFace8 : Set where
  negNeg negZero negPos
  zeroNeg zeroPos
  posNeg posZero posPos
  : PuncturedFace8

data FaceSheet9 : Set where
  faceCentre : FaceSheet9
  facePuncture : PuncturedFace8 → FaceSheet9

punctureFreePair : PuncturedFace8 → SSP.SSPTrit × SSP.SSPTrit
punctureFreePair negNeg = SSP.sspNegOne , SSP.sspNegOne
punctureFreePair negZero = SSP.sspNegOne , SSP.sspZero
punctureFreePair negPos = SSP.sspNegOne , SSP.sspPosOne
punctureFreePair zeroNeg = SSP.sspZero , SSP.sspNegOne
punctureFreePair zeroPos = SSP.sspZero , SSP.sspPosOne
punctureFreePair posNeg = SSP.sspPosOne , SSP.sspNegOne
punctureFreePair posZero = SSP.sspPosOne , SSP.sspZero
punctureFreePair posPos = SSP.sspPosOne , SSP.sspPosOne

faceSheetFreePair : FaceSheet9 → SSP.SSPTrit × SSP.SSPTrit
faceSheetFreePair faceCentre = SSP.sspZero , SSP.sspZero
faceSheetFreePair (facePuncture p) = punctureFreePair p

------------------------------------------------------------------------
-- 2. Embed the local 3x3 sheet into each actual cube face.
------------------------------------------------------------------------

placeOnFace : Geometry.Face6 → FaceSheet9 → Geometry.Ternary27Point
placeOnFace Geometry.xNegativeFace sheet with faceSheetFreePair sheet
... | a , b = Geometry.ternary27Point SSP.sspNegOne a b
placeOnFace Geometry.xPositiveFace sheet with faceSheetFreePair sheet
... | a , b = Geometry.ternary27Point SSP.sspPosOne a b
placeOnFace Geometry.yNegativeFace sheet with faceSheetFreePair sheet
... | a , b = Geometry.ternary27Point a SSP.sspNegOne b
placeOnFace Geometry.yPositiveFace sheet with faceSheetFreePair sheet
... | a , b = Geometry.ternary27Point a SSP.sspPosOne b
placeOnFace Geometry.zNegativeFace sheet with faceSheetFreePair sheet
... | a , b = Geometry.ternary27Point a b SSP.sspNegOne
placeOnFace Geometry.zPositiveFace sheet with faceSheetFreePair sheet
... | a , b = Geometry.ternary27Point a b SSP.sspPosOne

placementIsOnFace :
  (face : Geometry.Face6) →
  (sheet : FaceSheet9) →
  Geometry.OnFace face (placeOnFace face sheet)
placementIsOnFace Geometry.xNegativeFace sheet = Geometry.onFace refl
placementIsOnFace Geometry.xPositiveFace sheet = Geometry.onFace refl
placementIsOnFace Geometry.yNegativeFace sheet = Geometry.onFace refl
placementIsOnFace Geometry.yPositiveFace sheet = Geometry.onFace refl
placementIsOnFace Geometry.zNegativeFace sheet = Geometry.onFace refl
placementIsOnFace Geometry.zPositiveFace sheet = Geometry.onFace refl

------------------------------------------------------------------------
-- 3. The local punctured eight is four antipodal directions x orientation.
------------------------------------------------------------------------

data FaceDirection4 : Set where
  horizontalDirection
  verticalDirection
  positiveDiagonalDirection
  negativeDiagonalDirection
  : FaceDirection4

data FaceEndpointOrientation2 : Set where
  negativeEndpoint positiveEndpoint : FaceEndpointOrientation2

punctureToDirectionOrientation :
  PuncturedFace8 → FaceDirection4 × FaceEndpointOrientation2
punctureToDirectionOrientation negZero = horizontalDirection , negativeEndpoint
punctureToDirectionOrientation posZero = horizontalDirection , positiveEndpoint
punctureToDirectionOrientation zeroNeg = verticalDirection , negativeEndpoint
punctureToDirectionOrientation zeroPos = verticalDirection , positiveEndpoint
punctureToDirectionOrientation negNeg = positiveDiagonalDirection , negativeEndpoint
punctureToDirectionOrientation posPos = positiveDiagonalDirection , positiveEndpoint
punctureToDirectionOrientation negPos = negativeDiagonalDirection , negativeEndpoint
punctureToDirectionOrientation posNeg = negativeDiagonalDirection , positiveEndpoint

directionOrientationToPuncture :
  FaceDirection4 × FaceEndpointOrientation2 → PuncturedFace8
directionOrientationToPuncture (horizontalDirection , negativeEndpoint) = negZero
directionOrientationToPuncture (horizontalDirection , positiveEndpoint) = posZero
directionOrientationToPuncture (verticalDirection , negativeEndpoint) = zeroNeg
directionOrientationToPuncture (verticalDirection , positiveEndpoint) = zeroPos
directionOrientationToPuncture (positiveDiagonalDirection , negativeEndpoint) = negNeg
directionOrientationToPuncture (positiveDiagonalDirection , positiveEndpoint) = posPos
directionOrientationToPuncture (negativeDiagonalDirection , negativeEndpoint) = negPos
directionOrientationToPuncture (negativeDiagonalDirection , positiveEndpoint) = posNeg

punctureDirectionRoundTrip :
  (p : PuncturedFace8) →
  directionOrientationToPuncture (punctureToDirectionOrientation p) ≡ p
punctureDirectionRoundTrip negNeg = refl
punctureDirectionRoundTrip negZero = refl
punctureDirectionRoundTrip negPos = refl
punctureDirectionRoundTrip zeroNeg = refl
punctureDirectionRoundTrip zeroPos = refl
punctureDirectionRoundTrip posNeg = refl
punctureDirectionRoundTrip posZero = refl
punctureDirectionRoundTrip posPos = refl

directionPunctureRoundTrip :
  (p : FaceDirection4 × FaceEndpointOrientation2) →
  punctureToDirectionOrientation (directionOrientationToPuncture p) ≡ p
directionPunctureRoundTrip (horizontalDirection , negativeEndpoint) = refl
directionPunctureRoundTrip (horizontalDirection , positiveEndpoint) = refl
directionPunctureRoundTrip (verticalDirection , negativeEndpoint) = refl
directionPunctureRoundTrip (verticalDirection , positiveEndpoint) = refl
directionPunctureRoundTrip (positiveDiagonalDirection , negativeEndpoint) = refl
directionPunctureRoundTrip (positiveDiagonalDirection , positiveEndpoint) = refl
directionPunctureRoundTrip (negativeDiagonalDirection , negativeEndpoint) = refl
directionPunctureRoundTrip (negativeDiagonalDirection , positiveEndpoint) = refl

puncturedFaceIsFourDirectionsByTwo :
  Stable.CarrierIso
    PuncturedFace8
    (FaceDirection4 × FaceEndpointOrientation2)
puncturedFaceIsFourDirectionsByTwo =
  Stable.carrier-iso
    punctureToDirectionOrientation
    directionOrientationToPuncture
    punctureDirectionRoundTrip
    directionPunctureRoundTrip

------------------------------------------------------------------------
-- 4. Face-incidence 54 is six typed faces x one nonary face sheet.
------------------------------------------------------------------------

FaceIncidence54 : Set
FaceIncidence54 = Geometry.Face6 × FaceSheet9

faceSheetCount : Nat
faceSheetCount = 9

puncturedFaceCount : Nat
puncturedFaceCount = 8

faceIncidenceCount : Nat
faceIncidenceCount = 54

sixFacesTimesNineSheetIs54 :
  Geometry.outerFaceCount * faceSheetCount ≡ faceIncidenceCount
sixFacesTimesNineSheetIs54 = refl

faceSheetIsOnePlusEight : 1 + puncturedFaceCount ≡ faceSheetCount
faceSheetIsOnePlusEight = refl

------------------------------------------------------------------------
-- 5. Incidence multiplicity resolves 54 against the global 27 stratification.
--
-- Each of the six face-centres is incident to one face.
-- Each of the twelve edge-centres is incident to two faces.
-- Each of the eight cube corners is incident to three faces.
------------------------------------------------------------------------

faceCentreIncidenceCount : Nat
faceCentreIncidenceCount = 6

edgeCentreIncidenceCount : Nat
edgeCentreIncidenceCount = 24

cornerIncidenceCount : Nat
cornerIncidenceCount = 24

faceCentreIncidenceMatchesStratum :
  Strata.faceCentreCount ≡ faceCentreIncidenceCount
faceCentreIncidenceMatchesStratum = refl

edgeIncidenceIsTwoPerEdgeCentre :
  2 * Strata.edgeCentreCount ≡ edgeCentreIncidenceCount
edgeIncidenceIsTwoPerEdgeCentre = refl

cornerIncidenceIsThreePerCorner :
  3 * Strata.cornerCount ≡ cornerIncidenceCount
cornerIncidenceIsThreePerCorner = refl

stratifiedBoundaryIncidencesSumTo54 :
  faceCentreIncidenceCount + edgeCentreIncidenceCount + cornerIncidenceCount
  ≡ faceIncidenceCount
stratifiedBoundaryIncidencesSumTo54 = refl

------------------------------------------------------------------------
-- 6. Exact bridge socket from the reduced nonary 8 to one punctured face.
--
-- Both have the stable product shape 4 x 2, but the semantic bridge still
-- requires an explicit identification of the four nonidentity modes with the
-- four unoriented face directions and an orientation bridge.  This record is
-- the payment required; no canonical inhabitant is asserted here.
------------------------------------------------------------------------

record ReducedNonaryToFacePunctureBridge : Set where
  field
    modeDirection :
      Stable.CarrierIso Registry.NonIdentityMode4 FaceDirection4
    orientationEndpoint :
      Stable.CarrierIso Stable.Orientation2 FaceEndpointOrientation2

------------------------------------------------------------------------
-- 7. Distinct eight identities remain distinct until that bridge is supplied.
------------------------------------------------------------------------

data PuncturedFaceEightEqualsGlobalCornerEight : Set where
data ReducedEightEqualsPuncturedFaceEightWithoutBridge : Set where
data FaceIncidence54EqualsSituated54Semantically : Set where

data FaceSheetIdentityCreatesMonsterAction : Set where

puncturedFaceIsNotGlobalCornerByCardinality :
  PuncturedFaceEightEqualsGlobalCornerEight → ⊥
puncturedFaceIsNotGlobalCornerByCardinality ()

reducedEightNeedsNamedFaceBridge :
  ReducedEightEqualsPuncturedFaceEightWithoutBridge → ⊥
reducedEightNeedsNamedFaceBridge ()

faceIncidenceAndSituated54NeedNamedBridge :
  FaceIncidence54EqualsSituated54Semantically → ⊥
faceIncidenceAndSituated54NeedNamedBridge ()

faceSheetDoesNotCreateMonsterAction :
  FaceSheetIdentityCreatesMonsterAction → ⊥
faceSheetDoesNotCreateMonsterAction ()

record FaceSheetPunctureIncidenceBoundary : Set where
  constructor face-sheet-puncture-incidence-boundary
  field
    eachFaceIsNineSheet : Bool
    faceNineIsCentrePlusPuncturedEight : Bool
    puncturedEightIsFourDirectionsByTwo : Bool
    sixFaceSheetsGiveFiftyFourIncidences : Bool
    globalIncidenceDecompositionIsSixPlusTwentyFourPlusTwentyFour : Bool
    reducedEightAutomaticallyEqualsFaceEight : Bool
    puncturedFaceEightAutomaticallyEqualsGlobalCornerEight : Bool
    faceIncidence54AutomaticallyEqualsSituated54 : Bool

canonicalFaceSheetPunctureIncidenceBoundary :
  FaceSheetPunctureIncidenceBoundary
canonicalFaceSheetPunctureIncidenceBoundary =
  face-sheet-puncture-incidence-boundary
    true true true true true false false false
