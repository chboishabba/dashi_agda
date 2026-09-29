module DASHI.Moonshine.OggSSPP2F4FiniteChordTangentGroupLawExact where

------------------------------------------------------------------------
-- SOURCE-NATIVE F4 CHORD/TANGENT GEOMETRY AND THE EIGENPLANE LAW
--
-- This module calculates the genuine characteristic-two Weierstrass
-- chord/tangent coordinate formula, independently of the target triXor
-- addition. It then checks all 64 affine input pairs against the finite
-- addition table and all 81 rational input pairs against the 369 eigenchart.
--
-- It does NOT yet identify the source finite table with Mathlib's separate
-- WeierstrassCurve.Affine.Point.add definition.  That is the next Lean weld.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
import DASHI.Moonshine.OggSSPP2F4ZetaCurvePointEnumerationExact as Curve
import DASHI.Moonshine.OggSSPP2F4EllipticS3NineSheetBidiExact as Eigen
import DASHI.Moonshine.OggSSPP2F4RecenteredTriXorS3Exact as Plane
import Base369 as Base

-- Explicit characteristic-two reciprocal in F4; used only for nonzero
-- secant denominators.
reciprocal : Curve.F4 → Curve.F4
reciprocal Curve.zero₄ = Curve.zero₄
reciprocal Curve.one₄ = Curve.one₄
reciprocal Curve.zeta₄ = Curve.zetaSquared₄
reciprocal Curve.zetaSquared₄ = Curve.zeta₄

sameF4 : Curve.F4 → Curve.F4 → Bool
sameF4 Curve.zero₄ Curve.zero₄ = true
sameF4 Curve.one₄ Curve.one₄ = true
sameF4 Curve.zeta₄ Curve.zeta₄ = true
sameF4 Curve.zetaSquared₄ Curve.zetaSquared₄ = true
sameF4 _ _ = false

_and_ : Bool → Bool → Bool
true and b = b
false and b = false

isVertical : Curve.F4 → Curve.F4 → Curve.F4 → Curve.F4 → Bool
isVertical x y X Y =
  sameF4 x X and
  sameF4 (Curve._+₄_ y Y) Curve.one₄

-- Same x, nonvertical: tangent slope x².
-- Different x: secant slope (Y+y)/(X+x).
lineSlope : Curve.F4 → Curve.F4 → Curve.F4 → Curve.F4 → Curve.F4
lineSlope x y X Y with sameF4 x X
... | true = Curve.square₄ x
... | false =
  Curve._*₄_
    (Curve._+₄_ Y y)
    (reciprocal (Curve._+₄_ X x))

sumX : Curve.F4 → Curve.F4 → Curve.F4 → Curve.F4 → Curve.F4
sumX x y X Y =
  Curve._+₄_
    (Curve.square₄ (lineSlope x y X Y))
    (Curve._+₄_ x X)

-- The inverse of the third intersection has y-coordinate
--   slope*(x+sumX)+y+1.
sumY : Curve.F4 → Curve.F4 → Curve.F4 → Curve.F4 → Curve.F4
sumY x y X Y =
  Curve._+₄_
    (Curve._+₄_
      (Curve._*₄_
        (lineSlope x y X Y)
        (Curve._+₄_ x (sumX x y X Y)))
      y)
    Curve.one₄

data ChordReading : Set where
  atInfinity : ChordReading
  affineResult : Curve.F4 → Curve.F4 → ChordReading

arithmeticChordCoordinates :
  Curve.F4 → Curve.F4 → Curve.F4 → Curve.F4 → ChordReading
arithmeticChordCoordinates x y X Y with isVertical x y X Y
... | true = atInfinity
... | false = affineResult
  (sumX x y X Y)
  (sumY x y X Y)

arithmeticChord :
  Curve.AffineF4Point → Curve.AffineF4Point → ChordReading
arithmeticChord p q =
  arithmeticChordCoordinates
    (proj₁ (Curve.affineCoordinates p))
    (proj₂ (Curve.affineCoordinates p))
    (proj₁ (Curve.affineCoordinates q))
    (proj₂ (Curve.affineCoordinates q))

readRationalPoint : Curve.RationalF4Point → ChordReading
readRationalPoint Curve.infinity = atInfinity
readRationalPoint (Curve.affine p) =
  affineResult
    (proj₁ (Curve.affineCoordinates p))
    (proj₂ (Curve.affineCoordinates p))

------------------------------------------------------------------------
-- The independent finite chord/tangent table.
------------------------------------------------------------------------

chordSum :
  Curve.RationalF4Point → Curve.RationalF4Point → Curve.RationalF4Point
chordSum Curve.infinity q = q
chordSum (Curve.affine p) Curve.infinity = Curve.affine p
chordSum (Curve.affine Curve.p00) (Curve.affine Curve.p00) = Curve.affine Curve.p01
chordSum (Curve.affine Curve.p00) (Curve.affine Curve.p01) = Curve.infinity
chordSum (Curve.affine Curve.p00) (Curve.affine Curve.p1Zeta) = Curve.affine Curve.pZetaZeta
chordSum (Curve.affine Curve.p00) (Curve.affine Curve.p1ZetaSquared) = Curve.affine Curve.pZetaSquaredZetaSquared
chordSum (Curve.affine Curve.p00) (Curve.affine Curve.pZetaZeta) = Curve.affine Curve.pZetaSquaredZeta
chordSum (Curve.affine Curve.p00) (Curve.affine Curve.pZetaZetaSquared) = Curve.affine Curve.p1ZetaSquared
chordSum (Curve.affine Curve.p00) (Curve.affine Curve.pZetaSquaredZeta) = Curve.affine Curve.p1Zeta
chordSum (Curve.affine Curve.p00) (Curve.affine Curve.pZetaSquaredZetaSquared) = Curve.affine Curve.pZetaZetaSquared
chordSum (Curve.affine Curve.p01) (Curve.affine Curve.p00) = Curve.infinity
chordSum (Curve.affine Curve.p01) (Curve.affine Curve.p01) = Curve.affine Curve.p00
chordSum (Curve.affine Curve.p01) (Curve.affine Curve.p1Zeta) = Curve.affine Curve.pZetaSquaredZeta
chordSum (Curve.affine Curve.p01) (Curve.affine Curve.p1ZetaSquared) = Curve.affine Curve.pZetaZetaSquared
chordSum (Curve.affine Curve.p01) (Curve.affine Curve.pZetaZeta) = Curve.affine Curve.p1Zeta
chordSum (Curve.affine Curve.p01) (Curve.affine Curve.pZetaZetaSquared) = Curve.affine Curve.pZetaSquaredZetaSquared
chordSum (Curve.affine Curve.p01) (Curve.affine Curve.pZetaSquaredZeta) = Curve.affine Curve.pZetaZeta
chordSum (Curve.affine Curve.p01) (Curve.affine Curve.pZetaSquaredZetaSquared) = Curve.affine Curve.p1ZetaSquared
chordSum (Curve.affine Curve.p1Zeta) (Curve.affine Curve.p00) = Curve.affine Curve.pZetaZeta
chordSum (Curve.affine Curve.p1Zeta) (Curve.affine Curve.p01) = Curve.affine Curve.pZetaSquaredZeta
chordSum (Curve.affine Curve.p1Zeta) (Curve.affine Curve.p1Zeta) = Curve.affine Curve.p1ZetaSquared
chordSum (Curve.affine Curve.p1Zeta) (Curve.affine Curve.p1ZetaSquared) = Curve.infinity
chordSum (Curve.affine Curve.p1Zeta) (Curve.affine Curve.pZetaZeta) = Curve.affine Curve.pZetaSquaredZetaSquared
chordSum (Curve.affine Curve.p1Zeta) (Curve.affine Curve.pZetaZetaSquared) = Curve.affine Curve.p01
chordSum (Curve.affine Curve.p1Zeta) (Curve.affine Curve.pZetaSquaredZeta) = Curve.affine Curve.pZetaZetaSquared
chordSum (Curve.affine Curve.p1Zeta) (Curve.affine Curve.pZetaSquaredZetaSquared) = Curve.affine Curve.p00
chordSum (Curve.affine Curve.p1ZetaSquared) (Curve.affine Curve.p00) = Curve.affine Curve.pZetaSquaredZetaSquared
chordSum (Curve.affine Curve.p1ZetaSquared) (Curve.affine Curve.p01) = Curve.affine Curve.pZetaZetaSquared
chordSum (Curve.affine Curve.p1ZetaSquared) (Curve.affine Curve.p1Zeta) = Curve.infinity
chordSum (Curve.affine Curve.p1ZetaSquared) (Curve.affine Curve.p1ZetaSquared) = Curve.affine Curve.p1Zeta
chordSum (Curve.affine Curve.p1ZetaSquared) (Curve.affine Curve.pZetaZeta) = Curve.affine Curve.p00
chordSum (Curve.affine Curve.p1ZetaSquared) (Curve.affine Curve.pZetaZetaSquared) = Curve.affine Curve.pZetaSquaredZeta
chordSum (Curve.affine Curve.p1ZetaSquared) (Curve.affine Curve.pZetaSquaredZeta) = Curve.affine Curve.p01
chordSum (Curve.affine Curve.p1ZetaSquared) (Curve.affine Curve.pZetaSquaredZetaSquared) = Curve.affine Curve.pZetaZeta
chordSum (Curve.affine Curve.pZetaZeta) (Curve.affine Curve.p00) = Curve.affine Curve.pZetaSquaredZeta
chordSum (Curve.affine Curve.pZetaZeta) (Curve.affine Curve.p01) = Curve.affine Curve.p1Zeta
chordSum (Curve.affine Curve.pZetaZeta) (Curve.affine Curve.p1Zeta) = Curve.affine Curve.pZetaSquaredZetaSquared
chordSum (Curve.affine Curve.pZetaZeta) (Curve.affine Curve.p1ZetaSquared) = Curve.affine Curve.p00
chordSum (Curve.affine Curve.pZetaZeta) (Curve.affine Curve.pZetaZeta) = Curve.affine Curve.pZetaZetaSquared
chordSum (Curve.affine Curve.pZetaZeta) (Curve.affine Curve.pZetaZetaSquared) = Curve.infinity
chordSum (Curve.affine Curve.pZetaZeta) (Curve.affine Curve.pZetaSquaredZeta) = Curve.affine Curve.p1ZetaSquared
chordSum (Curve.affine Curve.pZetaZeta) (Curve.affine Curve.pZetaSquaredZetaSquared) = Curve.affine Curve.p01
chordSum (Curve.affine Curve.pZetaZetaSquared) (Curve.affine Curve.p00) = Curve.affine Curve.p1ZetaSquared
chordSum (Curve.affine Curve.pZetaZetaSquared) (Curve.affine Curve.p01) = Curve.affine Curve.pZetaSquaredZetaSquared
chordSum (Curve.affine Curve.pZetaZetaSquared) (Curve.affine Curve.p1Zeta) = Curve.affine Curve.p01
chordSum (Curve.affine Curve.pZetaZetaSquared) (Curve.affine Curve.p1ZetaSquared) = Curve.affine Curve.pZetaSquaredZeta
chordSum (Curve.affine Curve.pZetaZetaSquared) (Curve.affine Curve.pZetaZeta) = Curve.infinity
chordSum (Curve.affine Curve.pZetaZetaSquared) (Curve.affine Curve.pZetaZetaSquared) = Curve.affine Curve.pZetaZeta
chordSum (Curve.affine Curve.pZetaZetaSquared) (Curve.affine Curve.pZetaSquaredZeta) = Curve.affine Curve.p00
chordSum (Curve.affine Curve.pZetaZetaSquared) (Curve.affine Curve.pZetaSquaredZetaSquared) = Curve.affine Curve.p1Zeta
chordSum (Curve.affine Curve.pZetaSquaredZeta) (Curve.affine Curve.p00) = Curve.affine Curve.p1Zeta
chordSum (Curve.affine Curve.pZetaSquaredZeta) (Curve.affine Curve.p01) = Curve.affine Curve.pZetaZeta
chordSum (Curve.affine Curve.pZetaSquaredZeta) (Curve.affine Curve.p1Zeta) = Curve.affine Curve.pZetaZetaSquared
chordSum (Curve.affine Curve.pZetaSquaredZeta) (Curve.affine Curve.p1ZetaSquared) = Curve.affine Curve.p01
chordSum (Curve.affine Curve.pZetaSquaredZeta) (Curve.affine Curve.pZetaZeta) = Curve.affine Curve.p1ZetaSquared
chordSum (Curve.affine Curve.pZetaSquaredZeta) (Curve.affine Curve.pZetaZetaSquared) = Curve.affine Curve.p00
chordSum (Curve.affine Curve.pZetaSquaredZeta) (Curve.affine Curve.pZetaSquaredZeta) = Curve.affine Curve.pZetaSquaredZetaSquared
chordSum (Curve.affine Curve.pZetaSquaredZeta) (Curve.affine Curve.pZetaSquaredZetaSquared) = Curve.infinity
chordSum (Curve.affine Curve.pZetaSquaredZetaSquared) (Curve.affine Curve.p00) = Curve.affine Curve.pZetaZetaSquared
chordSum (Curve.affine Curve.pZetaSquaredZetaSquared) (Curve.affine Curve.p01) = Curve.affine Curve.p1ZetaSquared
chordSum (Curve.affine Curve.pZetaSquaredZetaSquared) (Curve.affine Curve.p1Zeta) = Curve.affine Curve.p00
chordSum (Curve.affine Curve.pZetaSquaredZetaSquared) (Curve.affine Curve.p1ZetaSquared) = Curve.affine Curve.pZetaZeta
chordSum (Curve.affine Curve.pZetaSquaredZetaSquared) (Curve.affine Curve.pZetaZeta) = Curve.affine Curve.p01
chordSum (Curve.affine Curve.pZetaSquaredZetaSquared) (Curve.affine Curve.pZetaZetaSquared) = Curve.affine Curve.p1Zeta
chordSum (Curve.affine Curve.pZetaSquaredZetaSquared) (Curve.affine Curve.pZetaSquaredZeta) = Curve.infinity
chordSum (Curve.affine Curve.pZetaSquaredZetaSquared) (Curve.affine Curve.pZetaSquaredZetaSquared) = Curve.affine Curve.pZetaSquaredZeta

-- Each clause computes F4 slopes, denominators, the third intersection
-- and characteristic-two elliptic negation, not the target ternary labels.
chordTableMatchesGeometry :
  (p q : Curve.AffineF4Point) →
  readRationalPoint (chordSum (Curve.affine p) (Curve.affine q))
    ≡ arithmeticChord p q
chordTableMatchesGeometry Curve.p00 Curve.p00 = refl
chordTableMatchesGeometry Curve.p00 Curve.p01 = refl
chordTableMatchesGeometry Curve.p00 Curve.p1Zeta = refl
chordTableMatchesGeometry Curve.p00 Curve.p1ZetaSquared = refl
chordTableMatchesGeometry Curve.p00 Curve.pZetaZeta = refl
chordTableMatchesGeometry Curve.p00 Curve.pZetaZetaSquared = refl
chordTableMatchesGeometry Curve.p00 Curve.pZetaSquaredZeta = refl
chordTableMatchesGeometry Curve.p00 Curve.pZetaSquaredZetaSquared = refl
chordTableMatchesGeometry Curve.p01 Curve.p00 = refl
chordTableMatchesGeometry Curve.p01 Curve.p01 = refl
chordTableMatchesGeometry Curve.p01 Curve.p1Zeta = refl
chordTableMatchesGeometry Curve.p01 Curve.p1ZetaSquared = refl
chordTableMatchesGeometry Curve.p01 Curve.pZetaZeta = refl
chordTableMatchesGeometry Curve.p01 Curve.pZetaZetaSquared = refl
chordTableMatchesGeometry Curve.p01 Curve.pZetaSquaredZeta = refl
chordTableMatchesGeometry Curve.p01 Curve.pZetaSquaredZetaSquared = refl
chordTableMatchesGeometry Curve.p1Zeta Curve.p00 = refl
chordTableMatchesGeometry Curve.p1Zeta Curve.p01 = refl
chordTableMatchesGeometry Curve.p1Zeta Curve.p1Zeta = refl
chordTableMatchesGeometry Curve.p1Zeta Curve.p1ZetaSquared = refl
chordTableMatchesGeometry Curve.p1Zeta Curve.pZetaZeta = refl
chordTableMatchesGeometry Curve.p1Zeta Curve.pZetaZetaSquared = refl
chordTableMatchesGeometry Curve.p1Zeta Curve.pZetaSquaredZeta = refl
chordTableMatchesGeometry Curve.p1Zeta Curve.pZetaSquaredZetaSquared = refl
chordTableMatchesGeometry Curve.p1ZetaSquared Curve.p00 = refl
chordTableMatchesGeometry Curve.p1ZetaSquared Curve.p01 = refl
chordTableMatchesGeometry Curve.p1ZetaSquared Curve.p1Zeta = refl
chordTableMatchesGeometry Curve.p1ZetaSquared Curve.p1ZetaSquared = refl
chordTableMatchesGeometry Curve.p1ZetaSquared Curve.pZetaZeta = refl
chordTableMatchesGeometry Curve.p1ZetaSquared Curve.pZetaZetaSquared = refl
chordTableMatchesGeometry Curve.p1ZetaSquared Curve.pZetaSquaredZeta = refl
chordTableMatchesGeometry Curve.p1ZetaSquared Curve.pZetaSquaredZetaSquared = refl
chordTableMatchesGeometry Curve.pZetaZeta Curve.p00 = refl
chordTableMatchesGeometry Curve.pZetaZeta Curve.p01 = refl
chordTableMatchesGeometry Curve.pZetaZeta Curve.p1Zeta = refl
chordTableMatchesGeometry Curve.pZetaZeta Curve.p1ZetaSquared = refl
chordTableMatchesGeometry Curve.pZetaZeta Curve.pZetaZeta = refl
chordTableMatchesGeometry Curve.pZetaZeta Curve.pZetaZetaSquared = refl
chordTableMatchesGeometry Curve.pZetaZeta Curve.pZetaSquaredZeta = refl
chordTableMatchesGeometry Curve.pZetaZeta Curve.pZetaSquaredZetaSquared = refl
chordTableMatchesGeometry Curve.pZetaZetaSquared Curve.p00 = refl
chordTableMatchesGeometry Curve.pZetaZetaSquared Curve.p01 = refl
chordTableMatchesGeometry Curve.pZetaZetaSquared Curve.p1Zeta = refl
chordTableMatchesGeometry Curve.pZetaZetaSquared Curve.p1ZetaSquared = refl
chordTableMatchesGeometry Curve.pZetaZetaSquared Curve.pZetaZeta = refl
chordTableMatchesGeometry Curve.pZetaZetaSquared Curve.pZetaZetaSquared = refl
chordTableMatchesGeometry Curve.pZetaZetaSquared Curve.pZetaSquaredZeta = refl
chordTableMatchesGeometry Curve.pZetaZetaSquared Curve.pZetaSquaredZetaSquared = refl
chordTableMatchesGeometry Curve.pZetaSquaredZeta Curve.p00 = refl
chordTableMatchesGeometry Curve.pZetaSquaredZeta Curve.p01 = refl
chordTableMatchesGeometry Curve.pZetaSquaredZeta Curve.p1Zeta = refl
chordTableMatchesGeometry Curve.pZetaSquaredZeta Curve.p1ZetaSquared = refl
chordTableMatchesGeometry Curve.pZetaSquaredZeta Curve.pZetaZeta = refl
chordTableMatchesGeometry Curve.pZetaSquaredZeta Curve.pZetaZetaSquared = refl
chordTableMatchesGeometry Curve.pZetaSquaredZeta Curve.pZetaSquaredZeta = refl
chordTableMatchesGeometry Curve.pZetaSquaredZeta Curve.pZetaSquaredZetaSquared = refl
chordTableMatchesGeometry Curve.pZetaSquaredZetaSquared Curve.p00 = refl
chordTableMatchesGeometry Curve.pZetaSquaredZetaSquared Curve.p01 = refl
chordTableMatchesGeometry Curve.pZetaSquaredZetaSquared Curve.p1Zeta = refl
chordTableMatchesGeometry Curve.pZetaSquaredZetaSquared Curve.p1ZetaSquared = refl
chordTableMatchesGeometry Curve.pZetaSquaredZetaSquared Curve.pZetaZeta = refl
chordTableMatchesGeometry Curve.pZetaSquaredZetaSquared Curve.pZetaZetaSquared = refl
chordTableMatchesGeometry Curve.pZetaSquaredZetaSquared Curve.pZetaSquaredZeta = refl
chordTableMatchesGeometry Curve.pZetaSquaredZetaSquared Curve.pZetaSquaredZetaSquared = refl

------------------------------------------------------------------------
-- This geometrically determined table has the original C3^2 addition,
-- in the actual arithmetic eigenbasis.
------------------------------------------------------------------------

chordSumEigenHom :
  (p q : Curve.RationalF4Point) →
  Eigen.curveToEigenPlane (chordSum p q)
    ≡ Plane.centerPlus
      (Eigen.curveToEigenPlane p)
      (Eigen.curveToEigenPlane q)
chordSumEigenHom (Curve.infinity) (Curve.infinity) = refl
chordSumEigenHom (Curve.infinity) (Curve.affine Curve.p00) = refl
chordSumEigenHom (Curve.infinity) (Curve.affine Curve.p01) = refl
chordSumEigenHom (Curve.infinity) (Curve.affine Curve.p1Zeta) = refl
chordSumEigenHom (Curve.infinity) (Curve.affine Curve.p1ZetaSquared) = refl
chordSumEigenHom (Curve.infinity) (Curve.affine Curve.pZetaZeta) = refl
chordSumEigenHom (Curve.infinity) (Curve.affine Curve.pZetaZetaSquared) = refl
chordSumEigenHom (Curve.infinity) (Curve.affine Curve.pZetaSquaredZeta) = refl
chordSumEigenHom (Curve.infinity) (Curve.affine Curve.pZetaSquaredZetaSquared) = refl
chordSumEigenHom (Curve.affine Curve.p00) (Curve.infinity) = refl
chordSumEigenHom (Curve.affine Curve.p00) (Curve.affine Curve.p00) = refl
chordSumEigenHom (Curve.affine Curve.p00) (Curve.affine Curve.p01) = refl
chordSumEigenHom (Curve.affine Curve.p00) (Curve.affine Curve.p1Zeta) = refl
chordSumEigenHom (Curve.affine Curve.p00) (Curve.affine Curve.p1ZetaSquared) = refl
chordSumEigenHom (Curve.affine Curve.p00) (Curve.affine Curve.pZetaZeta) = refl
chordSumEigenHom (Curve.affine Curve.p00) (Curve.affine Curve.pZetaZetaSquared) = refl
chordSumEigenHom (Curve.affine Curve.p00) (Curve.affine Curve.pZetaSquaredZeta) = refl
chordSumEigenHom (Curve.affine Curve.p00) (Curve.affine Curve.pZetaSquaredZetaSquared) = refl
chordSumEigenHom (Curve.affine Curve.p01) (Curve.infinity) = refl
chordSumEigenHom (Curve.affine Curve.p01) (Curve.affine Curve.p00) = refl
chordSumEigenHom (Curve.affine Curve.p01) (Curve.affine Curve.p01) = refl
chordSumEigenHom (Curve.affine Curve.p01) (Curve.affine Curve.p1Zeta) = refl
chordSumEigenHom (Curve.affine Curve.p01) (Curve.affine Curve.p1ZetaSquared) = refl
chordSumEigenHom (Curve.affine Curve.p01) (Curve.affine Curve.pZetaZeta) = refl
chordSumEigenHom (Curve.affine Curve.p01) (Curve.affine Curve.pZetaZetaSquared) = refl
chordSumEigenHom (Curve.affine Curve.p01) (Curve.affine Curve.pZetaSquaredZeta) = refl
chordSumEigenHom (Curve.affine Curve.p01) (Curve.affine Curve.pZetaSquaredZetaSquared) = refl
chordSumEigenHom (Curve.affine Curve.p1Zeta) (Curve.infinity) = refl
chordSumEigenHom (Curve.affine Curve.p1Zeta) (Curve.affine Curve.p00) = refl
chordSumEigenHom (Curve.affine Curve.p1Zeta) (Curve.affine Curve.p01) = refl
chordSumEigenHom (Curve.affine Curve.p1Zeta) (Curve.affine Curve.p1Zeta) = refl
chordSumEigenHom (Curve.affine Curve.p1Zeta) (Curve.affine Curve.p1ZetaSquared) = refl
chordSumEigenHom (Curve.affine Curve.p1Zeta) (Curve.affine Curve.pZetaZeta) = refl
chordSumEigenHom (Curve.affine Curve.p1Zeta) (Curve.affine Curve.pZetaZetaSquared) = refl
chordSumEigenHom (Curve.affine Curve.p1Zeta) (Curve.affine Curve.pZetaSquaredZeta) = refl
chordSumEigenHom (Curve.affine Curve.p1Zeta) (Curve.affine Curve.pZetaSquaredZetaSquared) = refl
chordSumEigenHom (Curve.affine Curve.p1ZetaSquared) (Curve.infinity) = refl
chordSumEigenHom (Curve.affine Curve.p1ZetaSquared) (Curve.affine Curve.p00) = refl
chordSumEigenHom (Curve.affine Curve.p1ZetaSquared) (Curve.affine Curve.p01) = refl
chordSumEigenHom (Curve.affine Curve.p1ZetaSquared) (Curve.affine Curve.p1Zeta) = refl
chordSumEigenHom (Curve.affine Curve.p1ZetaSquared) (Curve.affine Curve.p1ZetaSquared) = refl
chordSumEigenHom (Curve.affine Curve.p1ZetaSquared) (Curve.affine Curve.pZetaZeta) = refl
chordSumEigenHom (Curve.affine Curve.p1ZetaSquared) (Curve.affine Curve.pZetaZetaSquared) = refl
chordSumEigenHom (Curve.affine Curve.p1ZetaSquared) (Curve.affine Curve.pZetaSquaredZeta) = refl
chordSumEigenHom (Curve.affine Curve.p1ZetaSquared) (Curve.affine Curve.pZetaSquaredZetaSquared) = refl
chordSumEigenHom (Curve.affine Curve.pZetaZeta) (Curve.infinity) = refl
chordSumEigenHom (Curve.affine Curve.pZetaZeta) (Curve.affine Curve.p00) = refl
chordSumEigenHom (Curve.affine Curve.pZetaZeta) (Curve.affine Curve.p01) = refl
chordSumEigenHom (Curve.affine Curve.pZetaZeta) (Curve.affine Curve.p1Zeta) = refl
chordSumEigenHom (Curve.affine Curve.pZetaZeta) (Curve.affine Curve.p1ZetaSquared) = refl
chordSumEigenHom (Curve.affine Curve.pZetaZeta) (Curve.affine Curve.pZetaZeta) = refl
chordSumEigenHom (Curve.affine Curve.pZetaZeta) (Curve.affine Curve.pZetaZetaSquared) = refl
chordSumEigenHom (Curve.affine Curve.pZetaZeta) (Curve.affine Curve.pZetaSquaredZeta) = refl
chordSumEigenHom (Curve.affine Curve.pZetaZeta) (Curve.affine Curve.pZetaSquaredZetaSquared) = refl
chordSumEigenHom (Curve.affine Curve.pZetaZetaSquared) (Curve.infinity) = refl
chordSumEigenHom (Curve.affine Curve.pZetaZetaSquared) (Curve.affine Curve.p00) = refl
chordSumEigenHom (Curve.affine Curve.pZetaZetaSquared) (Curve.affine Curve.p01) = refl
chordSumEigenHom (Curve.affine Curve.pZetaZetaSquared) (Curve.affine Curve.p1Zeta) = refl
chordSumEigenHom (Curve.affine Curve.pZetaZetaSquared) (Curve.affine Curve.p1ZetaSquared) = refl
chordSumEigenHom (Curve.affine Curve.pZetaZetaSquared) (Curve.affine Curve.pZetaZeta) = refl
chordSumEigenHom (Curve.affine Curve.pZetaZetaSquared) (Curve.affine Curve.pZetaZetaSquared) = refl
chordSumEigenHom (Curve.affine Curve.pZetaZetaSquared) (Curve.affine Curve.pZetaSquaredZeta) = refl
chordSumEigenHom (Curve.affine Curve.pZetaZetaSquared) (Curve.affine Curve.pZetaSquaredZetaSquared) = refl
chordSumEigenHom (Curve.affine Curve.pZetaSquaredZeta) (Curve.infinity) = refl
chordSumEigenHom (Curve.affine Curve.pZetaSquaredZeta) (Curve.affine Curve.p00) = refl
chordSumEigenHom (Curve.affine Curve.pZetaSquaredZeta) (Curve.affine Curve.p01) = refl
chordSumEigenHom (Curve.affine Curve.pZetaSquaredZeta) (Curve.affine Curve.p1Zeta) = refl
chordSumEigenHom (Curve.affine Curve.pZetaSquaredZeta) (Curve.affine Curve.p1ZetaSquared) = refl
chordSumEigenHom (Curve.affine Curve.pZetaSquaredZeta) (Curve.affine Curve.pZetaZeta) = refl
chordSumEigenHom (Curve.affine Curve.pZetaSquaredZeta) (Curve.affine Curve.pZetaZetaSquared) = refl
chordSumEigenHom (Curve.affine Curve.pZetaSquaredZeta) (Curve.affine Curve.pZetaSquaredZeta) = refl
chordSumEigenHom (Curve.affine Curve.pZetaSquaredZeta) (Curve.affine Curve.pZetaSquaredZetaSquared) = refl
chordSumEigenHom (Curve.affine Curve.pZetaSquaredZetaSquared) (Curve.infinity) = refl
chordSumEigenHom (Curve.affine Curve.pZetaSquaredZetaSquared) (Curve.affine Curve.p00) = refl
chordSumEigenHom (Curve.affine Curve.pZetaSquaredZetaSquared) (Curve.affine Curve.p01) = refl
chordSumEigenHom (Curve.affine Curve.pZetaSquaredZetaSquared) (Curve.affine Curve.p1Zeta) = refl
chordSumEigenHom (Curve.affine Curve.pZetaSquaredZetaSquared) (Curve.affine Curve.p1ZetaSquared) = refl
chordSumEigenHom (Curve.affine Curve.pZetaSquaredZetaSquared) (Curve.affine Curve.pZetaZeta) = refl
chordSumEigenHom (Curve.affine Curve.pZetaSquaredZetaSquared) (Curve.affine Curve.pZetaZetaSquared) = refl
chordSumEigenHom (Curve.affine Curve.pZetaSquaredZetaSquared) (Curve.affine Curve.pZetaSquaredZeta) = refl
chordSumEigenHom (Curve.affine Curve.pZetaSquaredZetaSquared) (Curve.affine Curve.pZetaSquaredZetaSquared) = refl

chordSumHasActualZero :
  (p : Curve.RationalF4Point) →
  chordSum p Curve.infinity ≡ p
chordSumHasActualZero Curve.infinity = refl
chordSumHasActualZero (Curve.affine _) = refl

chordSumMatchesNegationOnDouble :
  (p : Curve.RationalF4Point) →
  chordSum p p ≡ Eigen.negCurve p
chordSumMatchesNegationOnDouble (Curve.infinity) = refl
chordSumMatchesNegationOnDouble (Curve.affine Curve.p00) = refl
chordSumMatchesNegationOnDouble (Curve.affine Curve.p01) = refl
chordSumMatchesNegationOnDouble (Curve.affine Curve.p1Zeta) = refl
chordSumMatchesNegationOnDouble (Curve.affine Curve.p1ZetaSquared) = refl
chordSumMatchesNegationOnDouble (Curve.affine Curve.pZetaZeta) = refl
chordSumMatchesNegationOnDouble (Curve.affine Curve.pZetaZetaSquared) = refl
chordSumMatchesNegationOnDouble (Curve.affine Curve.pZetaSquaredZeta) = refl
chordSumMatchesNegationOnDouble (Curve.affine Curve.pZetaSquaredZetaSquared) = refl

tripleChordSumIsInfinity :
  (p : Curve.RationalF4Point) →
  chordSum (chordSum p p) p ≡ Curve.infinity
tripleChordSumIsInfinity (Curve.infinity) = refl
tripleChordSumIsInfinity (Curve.affine Curve.p00) = refl
tripleChordSumIsInfinity (Curve.affine Curve.p01) = refl
tripleChordSumIsInfinity (Curve.affine Curve.p1Zeta) = refl
tripleChordSumIsInfinity (Curve.affine Curve.p1ZetaSquared) = refl
tripleChordSumIsInfinity (Curve.affine Curve.pZetaZeta) = refl
tripleChordSumIsInfinity (Curve.affine Curve.pZetaZetaSquared) = refl
tripleChordSumIsInfinity (Curve.affine Curve.pZetaSquaredZeta) = refl
tripleChordSumIsInfinity (Curve.affine Curve.pZetaSquaredZetaSquared) = refl

-- Selected basis in the actual finite field coordinate enumeration.
P : Curve.RationalF4Point
P = Curve.affine Curve.p00

Q : Curve.RationalF4Point
Q = Curve.affine Curve.p1Zeta

basisPAtOneZero :
  Eigen.curveToEigenPlane P
    ≡ (Base.tri-high , Base.tri-mid)
basisPAtOneZero = refl

basisQAtZeroOne :
  Eigen.curveToEigenPlane Q
    ≡ (Base.tri-mid , Base.tri-high)
basisQAtZeroOne = refl

PPlusQIsZetaZeta :
  chordSum P Q ≡ Curve.affine Curve.pZetaZeta
PPlusQIsZetaZeta = refl

------------------------------------------------------------------------
-- Arithmetic automorphisms genuinely respect this finite geometric law.
------------------------------------------------------------------------

frobeniusPreservesChordSum :
  (p q : Curve.AffineF4Point) →
  Curve.frobeniusRational
    (chordSum (Curve.affine p) (Curve.affine q))
    ≡ chordSum
       (Curve.frobeniusRational (Curve.affine p))
       (Curve.frobeniusRational (Curve.affine q))
frobeniusPreservesChordSum (Curve.affine Curve.p00) (Curve.affine Curve.p00) = refl
frobeniusPreservesChordSum (Curve.affine Curve.p00) (Curve.affine Curve.p01) = refl
frobeniusPreservesChordSum (Curve.affine Curve.p00) (Curve.affine Curve.p1Zeta) = refl
frobeniusPreservesChordSum (Curve.affine Curve.p00) (Curve.affine Curve.p1ZetaSquared) = refl
frobeniusPreservesChordSum (Curve.affine Curve.p00) (Curve.affine Curve.pZetaZeta) = refl
frobeniusPreservesChordSum (Curve.affine Curve.p00) (Curve.affine Curve.pZetaZetaSquared) = refl
frobeniusPreservesChordSum (Curve.affine Curve.p00) (Curve.affine Curve.pZetaSquaredZeta) = refl
frobeniusPreservesChordSum (Curve.affine Curve.p00) (Curve.affine Curve.pZetaSquaredZetaSquared) = refl
frobeniusPreservesChordSum (Curve.affine Curve.p01) (Curve.affine Curve.p00) = refl
frobeniusPreservesChordSum (Curve.affine Curve.p01) (Curve.affine Curve.p01) = refl
frobeniusPreservesChordSum (Curve.affine Curve.p01) (Curve.affine Curve.p1Zeta) = refl
frobeniusPreservesChordSum (Curve.affine Curve.p01) (Curve.affine Curve.p1ZetaSquared) = refl
frobeniusPreservesChordSum (Curve.affine Curve.p01) (Curve.affine Curve.pZetaZeta) = refl
frobeniusPreservesChordSum (Curve.affine Curve.p01) (Curve.affine Curve.pZetaZetaSquared) = refl
frobeniusPreservesChordSum (Curve.affine Curve.p01) (Curve.affine Curve.pZetaSquaredZeta) = refl
frobeniusPreservesChordSum (Curve.affine Curve.p01) (Curve.affine Curve.pZetaSquaredZetaSquared) = refl
frobeniusPreservesChordSum (Curve.affine Curve.p1Zeta) (Curve.affine Curve.p00) = refl
frobeniusPreservesChordSum (Curve.affine Curve.p1Zeta) (Curve.affine Curve.p01) = refl
frobeniusPreservesChordSum (Curve.affine Curve.p1Zeta) (Curve.affine Curve.p1Zeta) = refl
frobeniusPreservesChordSum (Curve.affine Curve.p1Zeta) (Curve.affine Curve.p1ZetaSquared) = refl
frobeniusPreservesChordSum (Curve.affine Curve.p1Zeta) (Curve.affine Curve.pZetaZeta) = refl
frobeniusPreservesChordSum (Curve.affine Curve.p1Zeta) (Curve.affine Curve.pZetaZetaSquared) = refl
frobeniusPreservesChordSum (Curve.affine Curve.p1Zeta) (Curve.affine Curve.pZetaSquaredZeta) = refl
frobeniusPreservesChordSum (Curve.affine Curve.p1Zeta) (Curve.affine Curve.pZetaSquaredZetaSquared) = refl
frobeniusPreservesChordSum (Curve.affine Curve.p1ZetaSquared) (Curve.affine Curve.p00) = refl
frobeniusPreservesChordSum (Curve.affine Curve.p1ZetaSquared) (Curve.affine Curve.p01) = refl
frobeniusPreservesChordSum (Curve.affine Curve.p1ZetaSquared) (Curve.affine Curve.p1Zeta) = refl
frobeniusPreservesChordSum (Curve.affine Curve.p1ZetaSquared) (Curve.affine Curve.p1ZetaSquared) = refl
frobeniusPreservesChordSum (Curve.affine Curve.p1ZetaSquared) (Curve.affine Curve.pZetaZeta) = refl
frobeniusPreservesChordSum (Curve.affine Curve.p1ZetaSquared) (Curve.affine Curve.pZetaZetaSquared) = refl
frobeniusPreservesChordSum (Curve.affine Curve.p1ZetaSquared) (Curve.affine Curve.pZetaSquaredZeta) = refl
frobeniusPreservesChordSum (Curve.affine Curve.p1ZetaSquared) (Curve.affine Curve.pZetaSquaredZetaSquared) = refl
frobeniusPreservesChordSum (Curve.affine Curve.pZetaZeta) (Curve.affine Curve.p00) = refl
frobeniusPreservesChordSum (Curve.affine Curve.pZetaZeta) (Curve.affine Curve.p01) = refl
frobeniusPreservesChordSum (Curve.affine Curve.pZetaZeta) (Curve.affine Curve.p1Zeta) = refl
frobeniusPreservesChordSum (Curve.affine Curve.pZetaZeta) (Curve.affine Curve.p1ZetaSquared) = refl
frobeniusPreservesChordSum (Curve.affine Curve.pZetaZeta) (Curve.affine Curve.pZetaZeta) = refl
frobeniusPreservesChordSum (Curve.affine Curve.pZetaZeta) (Curve.affine Curve.pZetaZetaSquared) = refl
frobeniusPreservesChordSum (Curve.affine Curve.pZetaZeta) (Curve.affine Curve.pZetaSquaredZeta) = refl
frobeniusPreservesChordSum (Curve.affine Curve.pZetaZeta) (Curve.affine Curve.pZetaSquaredZetaSquared) = refl
frobeniusPreservesChordSum (Curve.affine Curve.pZetaZetaSquared) (Curve.affine Curve.p00) = refl
frobeniusPreservesChordSum (Curve.affine Curve.pZetaZetaSquared) (Curve.affine Curve.p01) = refl
frobeniusPreservesChordSum (Curve.affine Curve.pZetaZetaSquared) (Curve.affine Curve.p1Zeta) = refl
frobeniusPreservesChordSum (Curve.affine Curve.pZetaZetaSquared) (Curve.affine Curve.p1ZetaSquared) = refl
frobeniusPreservesChordSum (Curve.affine Curve.pZetaZetaSquared) (Curve.affine Curve.pZetaZeta) = refl
frobeniusPreservesChordSum (Curve.affine Curve.pZetaZetaSquared) (Curve.affine Curve.pZetaZetaSquared) = refl
frobeniusPreservesChordSum (Curve.affine Curve.pZetaZetaSquared) (Curve.affine Curve.pZetaSquaredZeta) = refl
frobeniusPreservesChordSum (Curve.affine Curve.pZetaZetaSquared) (Curve.affine Curve.pZetaSquaredZetaSquared) = refl
frobeniusPreservesChordSum (Curve.affine Curve.pZetaSquaredZeta) (Curve.affine Curve.p00) = refl
frobeniusPreservesChordSum (Curve.affine Curve.pZetaSquaredZeta) (Curve.affine Curve.p01) = refl
frobeniusPreservesChordSum (Curve.affine Curve.pZetaSquaredZeta) (Curve.affine Curve.p1Zeta) = refl
frobeniusPreservesChordSum (Curve.affine Curve.pZetaSquaredZeta) (Curve.affine Curve.p1ZetaSquared) = refl
frobeniusPreservesChordSum (Curve.affine Curve.pZetaSquaredZeta) (Curve.affine Curve.pZetaZeta) = refl
frobeniusPreservesChordSum (Curve.affine Curve.pZetaSquaredZeta) (Curve.affine Curve.pZetaZetaSquared) = refl
frobeniusPreservesChordSum (Curve.affine Curve.pZetaSquaredZeta) (Curve.affine Curve.pZetaSquaredZeta) = refl
frobeniusPreservesChordSum (Curve.affine Curve.pZetaSquaredZeta) (Curve.affine Curve.pZetaSquaredZetaSquared) = refl
frobeniusPreservesChordSum (Curve.affine Curve.pZetaSquaredZetaSquared) (Curve.affine Curve.p00) = refl
frobeniusPreservesChordSum (Curve.affine Curve.pZetaSquaredZetaSquared) (Curve.affine Curve.p01) = refl
frobeniusPreservesChordSum (Curve.affine Curve.pZetaSquaredZetaSquared) (Curve.affine Curve.p1Zeta) = refl
frobeniusPreservesChordSum (Curve.affine Curve.pZetaSquaredZetaSquared) (Curve.affine Curve.p1ZetaSquared) = refl
frobeniusPreservesChordSum (Curve.affine Curve.pZetaSquaredZetaSquared) (Curve.affine Curve.pZetaZeta) = refl
frobeniusPreservesChordSum (Curve.affine Curve.pZetaSquaredZetaSquared) (Curve.affine Curve.pZetaZetaSquared) = refl
frobeniusPreservesChordSum (Curve.affine Curve.pZetaSquaredZetaSquared) (Curve.affine Curve.pZetaSquaredZeta) = refl
frobeniusPreservesChordSum (Curve.affine Curve.pZetaSquaredZetaSquared) (Curve.affine Curve.pZetaSquaredZetaSquared) = refl

shearPreservesChordSum :
  (p q : Curve.AffineF4Point) →
  Eigen.rhoCurve
    (chordSum (Curve.affine p) (Curve.affine q))
    ≡ chordSum
       (Eigen.rhoCurve (Curve.affine p))
       (Eigen.rhoCurve (Curve.affine q))
shearPreservesChordSum (Curve.affine Curve.p00) (Curve.affine Curve.p00) = refl
shearPreservesChordSum (Curve.affine Curve.p00) (Curve.affine Curve.p01) = refl
shearPreservesChordSum (Curve.affine Curve.p00) (Curve.affine Curve.p1Zeta) = refl
shearPreservesChordSum (Curve.affine Curve.p00) (Curve.affine Curve.p1ZetaSquared) = refl
shearPreservesChordSum (Curve.affine Curve.p00) (Curve.affine Curve.pZetaZeta) = refl
shearPreservesChordSum (Curve.affine Curve.p00) (Curve.affine Curve.pZetaZetaSquared) = refl
shearPreservesChordSum (Curve.affine Curve.p00) (Curve.affine Curve.pZetaSquaredZeta) = refl
shearPreservesChordSum (Curve.affine Curve.p00) (Curve.affine Curve.pZetaSquaredZetaSquared) = refl
shearPreservesChordSum (Curve.affine Curve.p01) (Curve.affine Curve.p00) = refl
shearPreservesChordSum (Curve.affine Curve.p01) (Curve.affine Curve.p01) = refl
shearPreservesChordSum (Curve.affine Curve.p01) (Curve.affine Curve.p1Zeta) = refl
shearPreservesChordSum (Curve.affine Curve.p01) (Curve.affine Curve.p1ZetaSquared) = refl
shearPreservesChordSum (Curve.affine Curve.p01) (Curve.affine Curve.pZetaZeta) = refl
shearPreservesChordSum (Curve.affine Curve.p01) (Curve.affine Curve.pZetaZetaSquared) = refl
shearPreservesChordSum (Curve.affine Curve.p01) (Curve.affine Curve.pZetaSquaredZeta) = refl
shearPreservesChordSum (Curve.affine Curve.p01) (Curve.affine Curve.pZetaSquaredZetaSquared) = refl
shearPreservesChordSum (Curve.affine Curve.p1Zeta) (Curve.affine Curve.p00) = refl
shearPreservesChordSum (Curve.affine Curve.p1Zeta) (Curve.affine Curve.p01) = refl
shearPreservesChordSum (Curve.affine Curve.p1Zeta) (Curve.affine Curve.p1Zeta) = refl
shearPreservesChordSum (Curve.affine Curve.p1Zeta) (Curve.affine Curve.p1ZetaSquared) = refl
shearPreservesChordSum (Curve.affine Curve.p1Zeta) (Curve.affine Curve.pZetaZeta) = refl
shearPreservesChordSum (Curve.affine Curve.p1Zeta) (Curve.affine Curve.pZetaZetaSquared) = refl
shearPreservesChordSum (Curve.affine Curve.p1Zeta) (Curve.affine Curve.pZetaSquaredZeta) = refl
shearPreservesChordSum (Curve.affine Curve.p1Zeta) (Curve.affine Curve.pZetaSquaredZetaSquared) = refl
shearPreservesChordSum (Curve.affine Curve.p1ZetaSquared) (Curve.affine Curve.p00) = refl
shearPreservesChordSum (Curve.affine Curve.p1ZetaSquared) (Curve.affine Curve.p01) = refl
shearPreservesChordSum (Curve.affine Curve.p1ZetaSquared) (Curve.affine Curve.p1Zeta) = refl
shearPreservesChordSum (Curve.affine Curve.p1ZetaSquared) (Curve.affine Curve.p1ZetaSquared) = refl
shearPreservesChordSum (Curve.affine Curve.p1ZetaSquared) (Curve.affine Curve.pZetaZeta) = refl
shearPreservesChordSum (Curve.affine Curve.p1ZetaSquared) (Curve.affine Curve.pZetaZetaSquared) = refl
shearPreservesChordSum (Curve.affine Curve.p1ZetaSquared) (Curve.affine Curve.pZetaSquaredZeta) = refl
shearPreservesChordSum (Curve.affine Curve.p1ZetaSquared) (Curve.affine Curve.pZetaSquaredZetaSquared) = refl
shearPreservesChordSum (Curve.affine Curve.pZetaZeta) (Curve.affine Curve.p00) = refl
shearPreservesChordSum (Curve.affine Curve.pZetaZeta) (Curve.affine Curve.p01) = refl
shearPreservesChordSum (Curve.affine Curve.pZetaZeta) (Curve.affine Curve.p1Zeta) = refl
shearPreservesChordSum (Curve.affine Curve.pZetaZeta) (Curve.affine Curve.p1ZetaSquared) = refl
shearPreservesChordSum (Curve.affine Curve.pZetaZeta) (Curve.affine Curve.pZetaZeta) = refl
shearPreservesChordSum (Curve.affine Curve.pZetaZeta) (Curve.affine Curve.pZetaZetaSquared) = refl
shearPreservesChordSum (Curve.affine Curve.pZetaZeta) (Curve.affine Curve.pZetaSquaredZeta) = refl
shearPreservesChordSum (Curve.affine Curve.pZetaZeta) (Curve.affine Curve.pZetaSquaredZetaSquared) = refl
shearPreservesChordSum (Curve.affine Curve.pZetaZetaSquared) (Curve.affine Curve.p00) = refl
shearPreservesChordSum (Curve.affine Curve.pZetaZetaSquared) (Curve.affine Curve.p01) = refl
shearPreservesChordSum (Curve.affine Curve.pZetaZetaSquared) (Curve.affine Curve.p1Zeta) = refl
shearPreservesChordSum (Curve.affine Curve.pZetaZetaSquared) (Curve.affine Curve.p1ZetaSquared) = refl
shearPreservesChordSum (Curve.affine Curve.pZetaZetaSquared) (Curve.affine Curve.pZetaZeta) = refl
shearPreservesChordSum (Curve.affine Curve.pZetaZetaSquared) (Curve.affine Curve.pZetaZetaSquared) = refl
shearPreservesChordSum (Curve.affine Curve.pZetaZetaSquared) (Curve.affine Curve.pZetaSquaredZeta) = refl
shearPreservesChordSum (Curve.affine Curve.pZetaZetaSquared) (Curve.affine Curve.pZetaSquaredZetaSquared) = refl
shearPreservesChordSum (Curve.affine Curve.pZetaSquaredZeta) (Curve.affine Curve.p00) = refl
shearPreservesChordSum (Curve.affine Curve.pZetaSquaredZeta) (Curve.affine Curve.p01) = refl
shearPreservesChordSum (Curve.affine Curve.pZetaSquaredZeta) (Curve.affine Curve.p1Zeta) = refl
shearPreservesChordSum (Curve.affine Curve.pZetaSquaredZeta) (Curve.affine Curve.p1ZetaSquared) = refl
shearPreservesChordSum (Curve.affine Curve.pZetaSquaredZeta) (Curve.affine Curve.pZetaZeta) = refl
shearPreservesChordSum (Curve.affine Curve.pZetaSquaredZeta) (Curve.affine Curve.pZetaZetaSquared) = refl
shearPreservesChordSum (Curve.affine Curve.pZetaSquaredZeta) (Curve.affine Curve.pZetaSquaredZeta) = refl
shearPreservesChordSum (Curve.affine Curve.pZetaSquaredZeta) (Curve.affine Curve.pZetaSquaredZetaSquared) = refl
shearPreservesChordSum (Curve.affine Curve.pZetaSquaredZetaSquared) (Curve.affine Curve.p00) = refl
shearPreservesChordSum (Curve.affine Curve.pZetaSquaredZetaSquared) (Curve.affine Curve.p01) = refl
shearPreservesChordSum (Curve.affine Curve.pZetaSquaredZetaSquared) (Curve.affine Curve.p1Zeta) = refl
shearPreservesChordSum (Curve.affine Curve.pZetaSquaredZetaSquared) (Curve.affine Curve.p1ZetaSquared) = refl
shearPreservesChordSum (Curve.affine Curve.pZetaSquaredZetaSquared) (Curve.affine Curve.pZetaZeta) = refl
shearPreservesChordSum (Curve.affine Curve.pZetaSquaredZetaSquared) (Curve.affine Curve.pZetaZetaSquared) = refl
shearPreservesChordSum (Curve.affine Curve.pZetaSquaredZetaSquared) (Curve.affine Curve.pZetaSquaredZeta) = refl
shearPreservesChordSum (Curve.affine Curve.pZetaSquaredZetaSquared) (Curve.affine Curve.pZetaSquaredZetaSquared) = refl

record FiniteChordTangentGroupBoundary : Set where
  constructor finite-chord-tangent-group-boundary
  field
    actualF4SlopeArithmeticUsed : Bool
    all64AffineChordComparisonsExact : Bool
    all81AdditionEigenchartComparisonsExact : Bool
    fullNinePointExponentThree : Bool
    selectedGeneratorsPAndQExplicit : Bool
    pPlusQZetaZetaPaid : Bool
    frobeniusAdditiveOnFiniteGeometricLaw : Bool
    rhoAdditiveOnFiniteGeometricLaw : Bool
    MathlibIndependentEllipticAdditionIdentified : Bool
    gammaZeroFourMarkingIdentified : Bool

canonicalFiniteChordTangentGroupBoundary : FiniteChordTangentGroupBoundary
canonicalFiniteChordTangentGroupBoundary =
  finite-chord-tangent-group-boundary
    true true true true true true true true false false
