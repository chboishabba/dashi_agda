module DASHI.Moonshine.OggSSPP2F4EllipticS3NineSheetBidiExact where

------------------------------------------------------------------------
-- FINITE SOURCE ARITHMETIC: E(F4) / FROBENIUS / ZETA SHEAR / NEGATION
--
-- Uses the independent actual finite-field coordinate enumeration of
-- E : y^2+y=x^3 over F4.  The chosen generators are (0,0) and (1,zeta).
-- The Frob/shear/negation orbit data determine the following 3x3
-- coordinate chart, with infinity at the central group identity.
--
-- This is a two-sided, S3- and negation-equivariant *set* equivalence.
-- The target group law is the re-centred legacy triXor group law.
-- Elliptic addition preservation is NOT inferred from action equivariance.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
import Base369 as Base
import DASHI.Moonshine.OggSSPP2F4ZetaCurvePointEnumerationExact as Curve
import DASHI.Moonshine.OggSSPP2F4RecenteredTriXorS3Exact as Plane
import DASHI.Moonshine.OggSSPP2F4CurveOriginCenteredSheet9Exact as OldChart
import DASHI.Codec.TriadicPAdicCodec as Codec
import DASHI.Algebra.Trit as Trit

------------------------------------------------------------------------
-- Independently arithmetic rho(x,y) = (zeta*x,y), infinity fixed.
------------------------------------------------------------------------

rhoAffine : Curve.AffineF4Point → Curve.AffineF4Point
rhoAffine Curve.p00 = Curve.p00
rhoAffine Curve.p01 = Curve.p01
rhoAffine Curve.p1Zeta = Curve.pZetaZeta
rhoAffine Curve.pZetaZeta = Curve.pZetaSquaredZeta
rhoAffine Curve.pZetaSquaredZeta = Curve.p1Zeta
rhoAffine Curve.p1ZetaSquared = Curve.pZetaZetaSquared
rhoAffine Curve.pZetaZetaSquared = Curve.pZetaSquaredZetaSquared
rhoAffine Curve.pZetaSquaredZetaSquared = Curve.p1ZetaSquared

rhoAffineIsActualZetaTimesX :
  (p : Curve.AffineF4Point) →
  Curve.affineCoordinates (rhoAffine p)
    ≡
  (Curve.zeta₄ Curve.*₄ proj₁ (Curve.affineCoordinates p) ,
   proj₂ (Curve.affineCoordinates p))
rhoAffineIsActualZetaTimesX Curve.p00 = refl
rhoAffineIsActualZetaTimesX Curve.p01 = refl
rhoAffineIsActualZetaTimesX Curve.p1Zeta = refl
rhoAffineIsActualZetaTimesX Curve.p1ZetaSquared = refl
rhoAffineIsActualZetaTimesX Curve.pZetaZeta = refl
rhoAffineIsActualZetaTimesX Curve.pZetaZetaSquared = refl
rhoAffineIsActualZetaTimesX Curve.pZetaSquaredZeta = refl
rhoAffineIsActualZetaTimesX Curve.pZetaSquaredZetaSquared = refl

rhoCurve : Curve.RationalF4Point → Curve.RationalF4Point
rhoCurve Curve.infinity = Curve.infinity
rhoCurve (Curve.affine p) = Curve.affine (rhoAffine p)

rhoCurveOrderThree :
  (p : Curve.RationalF4Point) →
  rhoCurve (rhoCurve (rhoCurve p)) ≡ p
rhoCurveOrderThree (Curve.infinity) = refl
rhoCurveOrderThree (Curve.affine Curve.p00) = refl
rhoCurveOrderThree (Curve.affine Curve.p01) = refl
rhoCurveOrderThree (Curve.affine Curve.p1Zeta) = refl
rhoCurveOrderThree (Curve.affine Curve.p1ZetaSquared) = refl
rhoCurveOrderThree (Curve.affine Curve.pZetaZeta) = refl
rhoCurveOrderThree (Curve.affine Curve.pZetaZetaSquared) = refl
rhoCurveOrderThree (Curve.affine Curve.pZetaSquaredZeta) = refl
rhoCurveOrderThree (Curve.affine Curve.pZetaSquaredZetaSquared) = refl

------------------------------------------------------------------------
-- Actual characteristic-two elliptic inverse: (x,y) -> (x,y+1).
------------------------------------------------------------------------

negAffine : Curve.AffineF4Point → Curve.AffineF4Point
negAffine Curve.p00 = Curve.p01
negAffine Curve.p01 = Curve.p00
negAffine Curve.p1Zeta = Curve.p1ZetaSquared
negAffine Curve.p1ZetaSquared = Curve.p1Zeta
negAffine Curve.pZetaZeta = Curve.pZetaZetaSquared
negAffine Curve.pZetaZetaSquared = Curve.pZetaZeta
negAffine Curve.pZetaSquaredZeta = Curve.pZetaSquaredZetaSquared
negAffine Curve.pZetaSquaredZetaSquared = Curve.pZetaSquaredZeta

negAffineCoordinates :
  (p : Curve.AffineF4Point) →
  Curve.affineCoordinates (negAffine p)
    ≡
  (proj₁ (Curve.affineCoordinates p) ,
   proj₂ (Curve.affineCoordinates p) Curve.+₄ Curve.one₄)
negAffineCoordinates Curve.p00 = refl
negAffineCoordinates Curve.p01 = refl
negAffineCoordinates Curve.p1Zeta = refl
negAffineCoordinates Curve.p1ZetaSquared = refl
negAffineCoordinates Curve.pZetaZeta = refl
negAffineCoordinates Curve.pZetaZetaSquared = refl
negAffineCoordinates Curve.pZetaSquaredZeta = refl
negAffineCoordinates Curve.pZetaSquaredZetaSquared = refl

negCurve : Curve.RationalF4Point → Curve.RationalF4Point
negCurve Curve.infinity = Curve.infinity
negCurve (Curve.affine p) = Curve.affine (negAffine p)

negCurveOrderTwo :
  (p : Curve.RationalF4Point) →
  negCurve (negCurve p) ≡ p
negCurveOrderTwo (Curve.infinity) = refl
negCurveOrderTwo (Curve.affine Curve.p00) = refl
negCurveOrderTwo (Curve.affine Curve.p01) = refl
negCurveOrderTwo (Curve.affine Curve.p1Zeta) = refl
negCurveOrderTwo (Curve.affine Curve.p1ZetaSquared) = refl
negCurveOrderTwo (Curve.affine Curve.pZetaZeta) = refl
negCurveOrderTwo (Curve.affine Curve.pZetaZetaSquared) = refl
negCurveOrderTwo (Curve.affine Curve.pZetaSquaredZeta) = refl
negCurveOrderTwo (Curve.affine Curve.pZetaSquaredZetaSquared) = refl

frobeniusConjugatesRho :
  (p : Curve.RationalF4Point) →
  Curve.frobeniusRational
    (rhoCurve (Curve.frobeniusRational p))
    ≡ rhoCurve (rhoCurve p)
frobeniusConjugatesRho (Curve.infinity) = refl
frobeniusConjugatesRho (Curve.affine Curve.p00) = refl
frobeniusConjugatesRho (Curve.affine Curve.p01) = refl
frobeniusConjugatesRho (Curve.affine Curve.p1Zeta) = refl
frobeniusConjugatesRho (Curve.affine Curve.p1ZetaSquared) = refl
frobeniusConjugatesRho (Curve.affine Curve.pZetaZeta) = refl
frobeniusConjugatesRho (Curve.affine Curve.pZetaZetaSquared) = refl
frobeniusConjugatesRho (Curve.affine Curve.pZetaSquaredZeta) = refl
frobeniusConjugatesRho (Curve.affine Curve.pZetaSquaredZetaSquared) = refl

------------------------------------------------------------------------
-- The eigenbasis labelling of all nine ACTUAL finite-field points.
------------------------------------------------------------------------

curveToEigenPlane :
  Curve.RationalF4Point → Plane.CenteredNine
curveToEigenPlane (Curve.infinity) = Base.tri-mid , Base.tri-mid
curveToEigenPlane (Curve.affine Curve.p00) = Base.tri-high , Base.tri-mid
curveToEigenPlane (Curve.affine Curve.p01) = Base.tri-low , Base.tri-mid
curveToEigenPlane (Curve.affine Curve.p1Zeta) = Base.tri-mid , Base.tri-high
curveToEigenPlane (Curve.affine Curve.p1ZetaSquared) = Base.tri-mid , Base.tri-low
curveToEigenPlane (Curve.affine Curve.pZetaZeta) = Base.tri-high , Base.tri-high
curveToEigenPlane (Curve.affine Curve.pZetaZetaSquared) = Base.tri-low , Base.tri-low
curveToEigenPlane (Curve.affine Curve.pZetaSquaredZeta) = Base.tri-low , Base.tri-high
curveToEigenPlane (Curve.affine Curve.pZetaSquaredZetaSquared) = Base.tri-high , Base.tri-low

eigenPlaneToCurve :
  Plane.CenteredNine → Curve.RationalF4Point
eigenPlaneToCurve (Base.tri-mid , Base.tri-mid) = Curve.infinity
eigenPlaneToCurve (Base.tri-high , Base.tri-mid) = Curve.affine Curve.p00
eigenPlaneToCurve (Base.tri-low , Base.tri-mid) = Curve.affine Curve.p01
eigenPlaneToCurve (Base.tri-mid , Base.tri-high) = Curve.affine Curve.p1Zeta
eigenPlaneToCurve (Base.tri-mid , Base.tri-low) = Curve.affine Curve.p1ZetaSquared
eigenPlaneToCurve (Base.tri-high , Base.tri-high) = Curve.affine Curve.pZetaZeta
eigenPlaneToCurve (Base.tri-low , Base.tri-low) = Curve.affine Curve.pZetaZetaSquared
eigenPlaneToCurve (Base.tri-low , Base.tri-high) = Curve.affine Curve.pZetaSquaredZeta
eigenPlaneToCurve (Base.tri-high , Base.tri-low) = Curve.affine Curve.pZetaSquaredZetaSquared

curveEigenRoundTrip :
  (p : Curve.RationalF4Point) →
  eigenPlaneToCurve (curveToEigenPlane p) ≡ p
curveEigenRoundTrip (Curve.infinity) = refl
curveEigenRoundTrip (Curve.affine Curve.p00) = refl
curveEigenRoundTrip (Curve.affine Curve.p01) = refl
curveEigenRoundTrip (Curve.affine Curve.p1Zeta) = refl
curveEigenRoundTrip (Curve.affine Curve.p1ZetaSquared) = refl
curveEigenRoundTrip (Curve.affine Curve.pZetaZeta) = refl
curveEigenRoundTrip (Curve.affine Curve.pZetaZetaSquared) = refl
curveEigenRoundTrip (Curve.affine Curve.pZetaSquaredZeta) = refl
curveEigenRoundTrip (Curve.affine Curve.pZetaSquaredZetaSquared) = refl

eigenCurveRoundTrip :
  (p : Plane.CenteredNine) →
  curveToEigenPlane (eigenPlaneToCurve p) ≡ p
eigenCurveRoundTrip (Base.tri-mid , Base.tri-mid) = refl
eigenCurveRoundTrip (Base.tri-high , Base.tri-mid) = refl
eigenCurveRoundTrip (Base.tri-low , Base.tri-mid) = refl
eigenCurveRoundTrip (Base.tri-mid , Base.tri-high) = refl
eigenCurveRoundTrip (Base.tri-mid , Base.tri-low) = refl
eigenCurveRoundTrip (Base.tri-high , Base.tri-high) = refl
eigenCurveRoundTrip (Base.tri-low , Base.tri-low) = refl
eigenCurveRoundTrip (Base.tri-low , Base.tri-high) = refl
eigenCurveRoundTrip (Base.tri-high , Base.tri-low) = refl

curveInfinityIsAdditiveZero :
  curveToEigenPlane Curve.infinity ≡ Plane.centerZero
curveInfinityIsAdditiveZero = refl

arithmeticFrobeniusIntertwines :
  (p : Curve.RationalF4Point) →
  curveToEigenPlane (Curve.frobeniusRational p)
    ≡ Plane.frobPlane (curveToEigenPlane p)
arithmeticFrobeniusIntertwines (Curve.infinity) = refl
arithmeticFrobeniusIntertwines (Curve.affine Curve.p00) = refl
arithmeticFrobeniusIntertwines (Curve.affine Curve.p01) = refl
arithmeticFrobeniusIntertwines (Curve.affine Curve.p1Zeta) = refl
arithmeticFrobeniusIntertwines (Curve.affine Curve.p1ZetaSquared) = refl
arithmeticFrobeniusIntertwines (Curve.affine Curve.pZetaZeta) = refl
arithmeticFrobeniusIntertwines (Curve.affine Curve.pZetaZetaSquared) = refl
arithmeticFrobeniusIntertwines (Curve.affine Curve.pZetaSquaredZeta) = refl
arithmeticFrobeniusIntertwines (Curve.affine Curve.pZetaSquaredZetaSquared) = refl

arithmeticShearIntertwines :
  (p : Curve.RationalF4Point) →
  curveToEigenPlane (rhoCurve p)
    ≡ Plane.shearPlane (curveToEigenPlane p)
arithmeticShearIntertwines (Curve.infinity) = refl
arithmeticShearIntertwines (Curve.affine Curve.p00) = refl
arithmeticShearIntertwines (Curve.affine Curve.p01) = refl
arithmeticShearIntertwines (Curve.affine Curve.p1Zeta) = refl
arithmeticShearIntertwines (Curve.affine Curve.p1ZetaSquared) = refl
arithmeticShearIntertwines (Curve.affine Curve.pZetaZeta) = refl
arithmeticShearIntertwines (Curve.affine Curve.pZetaZetaSquared) = refl
arithmeticShearIntertwines (Curve.affine Curve.pZetaSquaredZeta) = refl
arithmeticShearIntertwines (Curve.affine Curve.pZetaSquaredZetaSquared) = refl

arithmeticInverseIntertwines :
  (p : Curve.RationalF4Point) →
  curveToEigenPlane (negCurve p)
    ≡ Plane.centerMinus (curveToEigenPlane p)
arithmeticInverseIntertwines (Curve.infinity) = refl
arithmeticInverseIntertwines (Curve.affine Curve.p00) = refl
arithmeticInverseIntertwines (Curve.affine Curve.p01) = refl
arithmeticInverseIntertwines (Curve.affine Curve.p1Zeta) = refl
arithmeticInverseIntertwines (Curve.affine Curve.p1ZetaSquared) = refl
arithmeticInverseIntertwines (Curve.affine Curve.pZetaZeta) = refl
arithmeticInverseIntertwines (Curve.affine Curve.pZetaZetaSquared) = refl
arithmeticInverseIntertwines (Curve.affine Curve.pZetaSquaredZeta) = refl
arithmeticInverseIntertwines (Curve.affine Curve.pZetaSquaredZetaSquared) = refl

------------------------------------------------------------------------
-- Target formal additive group operation is transported, not claimed to
-- be the independently selected arithmetic elliptic group addition.
------------------------------------------------------------------------

candidateCurveAddition :
  Curve.RationalF4Point →
  Curve.RationalF4Point →
  Curve.RationalF4Point
candidateCurveAddition p q =
  eigenPlaneToCurve
    (Plane.centerPlus (curveToEigenPlane p) (curveToEigenPlane q))

candidateAdditionIntertwinesByDefinition :
  (p q : Curve.RationalF4Point) →
  curveToEigenPlane (candidateCurveAddition p q)
    ≡ Plane.centerPlus (curveToEigenPlane p) (curveToEigenPlane q)
candidateAdditionIntertwinesByDefinition p q =
  eigenCurveRoundTrip
    (Plane.centerPlus (curveToEigenPlane p) (curveToEigenPlane q))

-- This equation is the remaining arithmetic test, NOT a proved equality:
-- candidateCurveAddition p q = actual Mathlib E(F4) addition p +_E q.

record EllipticS3NineSheetBoundary : Set where
  constructor elliptic-s3-nine-sheet-boundary
  field
    actualZetaMultiplicationCoordinates : Bool
    actualCharacteristicTwoInverseCoordinates : Bool
    arithmeticOrderThreeShear : Bool
    arithmeticFrobeniusConjugatesShear : Bool
    exactNinePointTwoSidedEigenChart : Bool
    infinityAtRecenteredZero : Bool
    frobeniusReflectionIntertwining : Bool
    shearIntertwining : Bool
    inversionIntertwining : Bool
    arithmeticEllipticAdditionPreservation : Bool
    gammaZeroFourLevelRecognition : Bool

canonicalEllipticS3NineSheetBoundary : EllipticS3NineSheetBoundary
canonicalEllipticS3NineSheetBoundary =
  elliptic-s3-nine-sheet-boundary
    true true true true true true true true true false false
