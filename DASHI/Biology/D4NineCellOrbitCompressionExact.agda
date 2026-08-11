module DASHI.Biology.D4NineCellOrbitCompressionExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Jean-Pierre Serre,
-- "Linear Representations of Finite Groups", Springer, 1977.
-- DOI: 10.1007/978-1-4684-9458-7.
--
-- Thomas M. Cover and Joy A. Thomas,
-- "Elements of Information Theory", second edition, Wiley, 2006.
-- DOI: 10.1002/047174882X.
--
-- DASHI CONTRIBUTION
--
-- Construct the actual nine-cell D4 carrier, its centre/edge/corner orbit
-- quotient, and a lossless quotient-plus-residual codec.  This distinguishes
-- the three cell orbits from the five irreducible representation types and
-- prevents the numerical relation 5 x 2 - 1 = 9 from being mistaken for the
-- cause of the nine-cell carrier.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Biology.TernaryMonsterSymmetryCandidateExact as Candidate

data NineCell : Set where
  centre : NineCell
  north east south west : NineCell
  northWest northEast southEast southWest : NineCell

data CellOrbit : Set where
  centreOrbit edgeOrbit cornerOrbit : CellOrbit

orbitOf : NineCell → CellOrbit
orbitOf centre = centreOrbit
orbitOf north = edgeOrbit
orbitOf east = edgeOrbit
orbitOf south = edgeOrbit
orbitOf west = edgeOrbit
orbitOf northWest = cornerOrbit
orbitOf northEast = cornerOrbit
orbitOf southEast = cornerOrbit
orbitOf southWest = cornerOrbit

orbitSize : CellOrbit → Nat
orbitSize centreOrbit = 1
orbitSize edgeOrbit = 4
orbitSize cornerOrbit = 4

nineCellOrbitCount :
  orbitSize centreOrbit + orbitSize edgeOrbit + orbitSize cornerOrbit ≡ 9
nineCellOrbitCount = refl

rotate90 : NineCell → NineCell
rotate90 centre = centre
rotate90 north = east
rotate90 east = south
rotate90 south = west
rotate90 west = north
rotate90 northWest = northEast
rotate90 northEast = southEast
rotate90 southEast = southWest
rotate90 southWest = northWest

reflectVertical : NineCell → NineCell
reflectVertical centre = centre
reflectVertical north = north
reflectVertical east = west
reflectVertical south = south
reflectVertical west = east
reflectVertical northWest = northEast
reflectVertical northEast = northWest
reflectVertical southEast = southWest
reflectVertical southWest = southEast

rotateFourTimes :
  (cell : NineCell) →
  rotate90 (rotate90 (rotate90 (rotate90 cell))) ≡ cell
rotateFourTimes centre = refl
rotateFourTimes north = refl
rotateFourTimes east = refl
rotateFourTimes south = refl
rotateFourTimes west = refl
rotateFourTimes northWest = refl
rotateFourTimes northEast = refl
rotateFourTimes southEast = refl
rotateFourTimes southWest = refl

reflectVerticalInvolutive :
  (cell : NineCell) →
  reflectVertical (reflectVertical cell) ≡ cell
reflectVerticalInvolutive centre = refl
reflectVerticalInvolutive north = refl
reflectVerticalInvolutive east = refl
reflectVerticalInvolutive south = refl
reflectVerticalInvolutive west = refl
reflectVerticalInvolutive northWest = refl
reflectVerticalInvolutive northEast = refl
reflectVerticalInvolutive southEast = refl
reflectVerticalInvolutive southWest = refl

orbitRotationInvariant :
  (cell : NineCell) →
  orbitOf (rotate90 cell) ≡ orbitOf cell
orbitRotationInvariant centre = refl
orbitRotationInvariant north = refl
orbitRotationInvariant east = refl
orbitRotationInvariant south = refl
orbitRotationInvariant west = refl
orbitRotationInvariant northWest = refl
orbitRotationInvariant northEast = refl
orbitRotationInvariant southEast = refl
orbitRotationInvariant southWest = refl

orbitReflectionInvariant :
  (cell : NineCell) →
  orbitOf (reflectVertical cell) ≡ orbitOf cell
orbitReflectionInvariant centre = refl
orbitReflectionInvariant north = refl
orbitReflectionInvariant east = refl
orbitReflectionInvariant south = refl
orbitReflectionInvariant west = refl
orbitReflectionInvariant northWest = refl
orbitReflectionInvariant northEast = refl
orbitReflectionInvariant southEast = refl
orbitReflectionInvariant southWest = refl

data CellResidual : CellOrbit → Set where
  fixedCentre : CellResidual centreOrbit
  edgeNorth edgeEast edgeSouth edgeWest : CellResidual edgeOrbit
  cornerNorthWest cornerNorthEast cornerSouthEast cornerSouthWest :
    CellResidual cornerOrbit

encodeCell :
  (cell : NineCell) →
  Σ CellOrbit CellResidual
encodeCell centre = centreOrbit , fixedCentre
encodeCell north = edgeOrbit , edgeNorth
encodeCell east = edgeOrbit , edgeEast
encodeCell south = edgeOrbit , edgeSouth
encodeCell west = edgeOrbit , edgeWest
encodeCell northWest = cornerOrbit , cornerNorthWest
encodeCell northEast = cornerOrbit , cornerNorthEast
encodeCell southEast = cornerOrbit , cornerSouthEast
encodeCell southWest = cornerOrbit , cornerSouthWest

decodeCell :
  Σ CellOrbit CellResidual →
  NineCell
decodeCell (centreOrbit , fixedCentre) = centre
decodeCell (edgeOrbit , edgeNorth) = north
decodeCell (edgeOrbit , edgeEast) = east
decodeCell (edgeOrbit , edgeSouth) = south
decodeCell (edgeOrbit , edgeWest) = west
decodeCell (cornerOrbit , cornerNorthWest) = northWest
decodeCell (cornerOrbit , cornerNorthEast) = northEast
decodeCell (cornerOrbit , cornerSouthEast) = southEast
decodeCell (cornerOrbit , cornerSouthWest) = southWest

decodeAfterEncode :
  (cell : NineCell) →
  decodeCell (encodeCell cell) ≡ cell
decodeAfterEncode centre = refl
decodeAfterEncode north = refl
decodeAfterEncode east = refl
decodeAfterEncode south = refl
decodeAfterEncode west = refl
decodeAfterEncode northWest = refl
decodeAfterEncode northEast = refl
decodeAfterEncode southEast = refl
decodeAfterEncode southWest = refl

encodeAfterDecode :
  (code : Σ CellOrbit CellResidual) →
  encodeCell (decodeCell code) ≡ code
encodeAfterDecode (centreOrbit , fixedCentre) = refl
encodeAfterDecode (edgeOrbit , edgeNorth) = refl
encodeAfterDecode (edgeOrbit , edgeEast) = refl
encodeAfterDecode (edgeOrbit , edgeSouth) = refl
encodeAfterDecode (edgeOrbit , edgeWest) = refl
encodeAfterDecode (cornerOrbit , cornerNorthWest) = refl
encodeAfterDecode (cornerOrbit , cornerNorthEast) = refl
encodeAfterDecode (cornerOrbit , cornerSouthEast) = refl
encodeAfterDecode (cornerOrbit , cornerSouthWest) = refl

canonicalD4IrrepKinds : List Candidate.D4IrrepKind
canonicalD4IrrepKinds =
  Candidate.A1 ∷ Candidate.A2 ∷ Candidate.B1
  ∷ Candidate.B2 ∷ Candidate.E2 ∷ []

listCount : ∀ {A : Set} → List A → Nat
listCount [] = 0
listCount (_ ∷ rest) = 1 + listCount rest

d4IrrepKindCountIsFive :
  listCount canonicalD4IrrepKinds ≡ 5
d4IrrepKindCountIsFive = refl

rawPermutationDimensionIsNine :
  Candidate.rawNineRepresentationDimension ≡ 9
rawPermutationDimensionIsNine =
  Candidate.rawNineRepresentationDimensionIsNine

rawPermutationA2Absent :
  Candidate.rawNineMultiplicity Candidate.A2 ≡ 0
rawPermutationA2Absent =
  Candidate.rawA2MultiplicityIsZero

record D4NineCellBoundary : Set where
  constructor d4NineCellBoundary
  field
    threeCellOrbitsEqualFiveIrrepTypes : Bool
    threeCellOrbitsEqualFiveIrrepTypesIsFalse :
      threeCellOrbitsEqualFiveIrrepTypes ≡ false
    fiveIrrepTypesExplainMonsterFiveAdicExponent : Bool
    fiveIrrepTypesExplainMonsterFiveAdicExponentIsFalse :
      fiveIrrepTypesExplainMonsterFiveAdicExponent ≡ false
    quotientWithoutResidualIsLossless : Bool
    quotientWithoutResidualIsLosslessIsFalse :
      quotientWithoutResidualIsLossless ≡ false
    codecRoundTripsExactly : Bool
    codecRoundTripsExactlyIsTrue :
      codecRoundTripsExactly ≡ true

canonicalD4NineCellBoundary : D4NineCellBoundary
canonicalD4NineCellBoundary =
  d4NineCellBoundary false refl false refl false refl true refl
