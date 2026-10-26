module DASHI.Moonshine.JInvariant369Cube27CuspCodecNonIsometryExact where

-- IMPORTANT USER GEOMETRY:
-- 27 is primarily the genuine 3 x 3 x 3 spatial balanced-ternary
-- cube, NOT a 27-cycle, a modular principal-level 27 point,
-- or the order of a Monster element.
--
-- An explicit finite DIGIT CODE joins its 27 positions to Z/27.
-- This map is a chart bijection only, not an isometry, a graph
-- automorphism, nor an intertwiner of arbitrary physical actions.
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import DASHI.Physics.Closure.BalancedTernaryContinuousEnvelope
  using (Trit; neg; zer; pos; []; _∷_)

import DASHI.Foundations.Base369Ternary27HypervoxelFabricGeometryExact as Cube
import DASHI.Foundations.SSPTritCarrier as SSP
import DASHI.Foundations.TriadicFiniteQuotient as Q
import DASHI.Algebra.TriadicFiniteArithmetic as Arithmetic

-- These wrappers stop spatial/cyclic/Monster group order being silently
-- conflated. Order-27 Monster objects require additional group data.
record SpatialCube27 : Set where
  constructor spatial-cube27
  field point : Cube.Ternary27Point

record PrincipalCusp27 : Set where
  constructor principal-cusp27
  field digitCode : Q.Residue3Pow 3

sspToDigit : SSP.SSPTrit → Trit
sspToDigit SSP.sspNegOne = neg
sspToDigit SSP.sspZero = zer
sspToDigit SSP.sspPosOne = pos

digitToSSP : Trit → SSP.SSPTrit
digitToSSP neg = SSP.sspNegOne
digitToSSP zer = SSP.sspZero
digitToSSP pos = SSP.sspPosOne

sspDigitRoundTrip : (t : SSP.SSPTrit) →
  digitToSSP (sspToDigit t) ≡ t
sspDigitRoundTrip SSP.sspNegOne = refl
sspDigitRoundTrip SSP.sspZero = refl
sspDigitRoundTrip SSP.sspPosOne = refl

digitSSPRoundTrip : (t : Trit) →
  sspToDigit (digitToSSP t) ≡ t
digitSSPRoundTrip neg = refl
digitSSPRoundTrip zer = refl
digitSSPRoundTrip pos = refl

encodeCubeDigits : Cube.Ternary27Point → Q.Residue3Pow 3
encodeCubeDigits (Cube.ternary27Point x y z) =
  sspToDigit x ∷ sspToDigit y ∷ sspToDigit z ∷ []

decodeCubeDigits : Q.Residue3Pow 3 → Cube.Ternary27Point
decodeCubeDigits (x ∷ y ∷ z ∷ []) =
  Cube.ternary27Point (digitToSSP x) (digitToSSP y) (digitToSSP z)

decodeEncodeCube : (p : Cube.Ternary27Point) →
  decodeCubeDigits (encodeCubeDigits p) ≡ p
decodeEncodeCube (Cube.ternary27Point x y z)
  rewrite sspDigitRoundTrip x
        | sspDigitRoundTrip y
        | sspDigitRoundTrip z = refl

encodeDecodeCube : (digits : Q.Residue3Pow 3) →
  encodeCubeDigits (decodeCubeDigits digits) ≡ digits
encodeDecodeCube (x ∷ y ∷ z ∷ [])
  rewrite digitSSPRoundTrip x
        | digitSSPRoundTrip y
        | digitSSPRoundTrip z = refl

-- Coordinate chart from literal geometry to an explicitly TAGGED cusp
-- code; construction goes through the native 3-trit cube, never through
-- a fresh 27-state substitute.
cubeToCusp : SpatialCube27 → PrincipalCusp27
cubeToCusp (spatial-cube27 p) =
  principal-cusp27 (encodeCubeDigits p)

cuspToCube : PrincipalCusp27 → SpatialCube27
cuspToCube (principal-cusp27 digits) =
  spatial-cube27 (decodeCubeDigits digits)

cubeCuspRoundTrip : (p : SpatialCube27) →
  cuspToCube (cubeToCusp p) ≡ p
cubeCuspRoundTrip (spatial-cube27 p)
  rewrite decodeEncodeCube p = refl

cuspCubeRoundTrip : (p : PrincipalCusp27) →
  cubeToCusp (cuspToCube p) ≡ p
cuspCubeRoundTrip (principal-cusp27 digits)
  rewrite encodeDecodeCube digits = refl

unit27 : Q.Residue3Pow 3
unit27 = pos ∷ zer ∷ zer ∷ []

addOneCusp : Q.Residue3Pow 3 → Q.Residue3Pow 3
addOneCusp = Arithmetic.addResidue unit27

-- The cube's geometric POSITIVE CORNER is (+1,+1,+1), index +13.
-- Cyclic residue +1 wraps it to (-1,-1,-1), index -13 mod 27.
-- This is a 6-coordinate-unit jump, NOT an edge of the cube.
residueCarryWrapsSpatialCorners :
  addOneCusp (encodeCubeDigits Cube.positiveCorner)
  ≡ encodeCubeDigits Cube.negativeCorner
residueCarryWrapsSpatialCorners = refl

wrappedCornersAreNotGridAdjacent :
  Cube.HypervoxelAdjacent Cube.positiveCorner Cube.negativeCorner → ⊥
wrappedCornersAreNotGridAdjacent ()

-- Consequently the finite code does not identify the cyclic cusp
-- translation T with a nearest-neighbour spatial cube motion.
