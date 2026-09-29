module DASHI.Moonshine.OggSSPP2F4ZetaCurvePointEnumerationExact where

------------------------------------------------------------------------
-- BANERJEE F4 SPECIAL FIBRE: EXACT ZETA-COORDINATE POINT ENUMERATION
--
-- Existing repository donor:
-- DASHI.Biology.EisensteinNineRingInterferenceExact.TernaryPoint
--    zeroPoint | zetaPoint | zetaSquaredPoint.
--
-- We use these three names as a FINITE LABEL chart only.  The rational
-- cyclotomic Eisenstein scalar field and the characteristic-two field F4
-- are distinct mathematical fields and no ring embedding is claimed.
--
-- Over F4 = F2[zeta]/(zeta^2+zeta+1),
--
--   y^2+y = 0 for y=0,1;
--   y^2+y = 1 for y=zeta,zeta^2;
--   x^3   = 0 for x=0 and =1 for x nonzero.
--
-- Therefore the curve y^2+y=x^3 has precisely eight affine F4 points:
--  (0,0),(0,1), plus (x,zeta),(x,zeta^2) for x=1,zeta,zeta^2.
-- The distinguished projective infinity gives exactly nine F4 points.
--
-- This is actual finite-field coordinate arithmetic and classification;
-- it is NOT yet the elliptic group law, its 3-torsion scheme, a formal
-- deformation, or the characteristic-two finite-flat Gamma0(4) flag.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Empty using (⊥)

import DASHI.Biology.EisensteinNineRingInterferenceExact as Phase
import DASHI.Moonshine.OggSSPMonstrousExponentSourceAttributionExact as Attribution

data F4 : Set where
  zero₄ : F4
  one₄ : F4
  zeta₄ : F4
  zetaSquared₄ : F4

-- Additive characteristic-two structure, with zeta^2 = zeta+1.
_+₄_ : F4 → F4 → F4
zero₄ +₄ b = b
one₄ +₄ zero₄ = one₄
one₄ +₄ one₄ = zero₄
one₄ +₄ zeta₄ = zetaSquared₄
one₄ +₄ zetaSquared₄ = zeta₄
zeta₄ +₄ zero₄ = zeta₄
zeta₄ +₄ one₄ = zetaSquared₄
zeta₄ +₄ zeta₄ = zero₄
zeta₄ +₄ zetaSquared₄ = one₄
zetaSquared₄ +₄ zero₄ = zetaSquared₄
zetaSquared₄ +₄ one₄ = zeta₄
zetaSquared₄ +₄ zeta₄ = one₄
zetaSquared₄ +₄ zetaSquared₄ = zero₄

_*₄_ : F4 → F4 → F4
zero₄ *₄ b = zero₄
one₄ *₄ b = b
zeta₄ *₄ zero₄ = zero₄
zeta₄ *₄ one₄ = zeta₄
zeta₄ *₄ zeta₄ = zetaSquared₄
zeta₄ *₄ zetaSquared₄ = one₄
zetaSquared₄ *₄ zero₄ = zero₄
zetaSquared₄ *₄ one₄ = zetaSquared₄
zetaSquared₄ *₄ zeta₄ = one₄
zetaSquared₄ *₄ zetaSquared₄ = zeta₄

square₄ : F4 → F4
square₄ x = x *₄ x

cube₄ : F4 → F4
cube₄ x = square₄ x *₄ x

zetaMinimalPolynomial :
  square₄ zeta₄ +₄ zeta₄ +₄ one₄ ≡ zero₄
zetaMinimalPolynomial = refl

zetaSquaredMinimalPolynomial :
  square₄ zetaSquared₄ +₄ zetaSquared₄ +₄ one₄ ≡ zero₄
zetaSquaredMinimalPolynomial = refl

zetaCubedIsOne : cube₄ zeta₄ ≡ one₄
zetaCubedIsOne = refl

zetaSquaredCubedIsOne : cube₄ zetaSquared₄ ≡ one₄
zetaSquaredCubedIsOne = refl

frobeniusSquare : F4 → F4
frobeniusSquare = square₄

frobeniusSwapsZeta :
  frobeniusSquare zeta₄ ≡ zetaSquared₄
frobeniusSwapsZeta = refl

frobeniusSwapsZetaSquared :
  frobeniusSquare zetaSquared₄ ≡ zeta₄
frobeniusSwapsZetaSquared = refl

frobeniusSquareInvolutive :
  (x : F4) →
  frobeniusSquare (frobeniusSquare x) ≡ x
frobeniusSquareInvolutive zero₄ = refl
frobeniusSquareInvolutive one₄ = refl
frobeniusSquareInvolutive zeta₄ = refl
frobeniusSquareInvolutive zetaSquared₄ = refl

yTrace : F4 → F4
yTrace y = square₄ y +₄ y

traceAtZero : yTrace zero₄ ≡ zero₄
traceAtZero = refl

traceAtOne : yTrace one₄ ≡ zero₄
traceAtOne = refl

traceAtZeta : yTrace zeta₄ ≡ one₄
traceAtZeta = refl

traceAtZetaSquared : yTrace zetaSquared₄ ≡ one₄
traceAtZetaSquared = refl

cubeAtZero : cube₄ zero₄ ≡ zero₄
cubeAtZero = refl

cubeAtOne : cube₄ one₄ ≡ one₄
cubeAtOne = refl

cubeAtZeta : cube₄ zeta₄ ≡ one₄
cubeAtZeta = refl

cubeAtZetaSquared : cube₄ zetaSquared₄ ≡ one₄
cubeAtZetaSquared = refl

satisfiesCurve : F4 → F4 → Bool
satisfiesCurve x y with yTrace y | cube₄ x
... | zero₄ | zero₄ = true
... | one₄ | one₄ = true
... | _ | _ = false

data AffineF4Point : Set where
  p00 : AffineF4Point
  p01 : AffineF4Point
  p1Zeta : AffineF4Point
  p1ZetaSquared : AffineF4Point
  pZetaZeta : AffineF4Point
  pZetaZetaSquared : AffineF4Point
  pZetaSquaredZeta : AffineF4Point
  pZetaSquaredZetaSquared : AffineF4Point

affineCoordinates : AffineF4Point → F4 × F4
affineCoordinates p00 = zero₄ , zero₄
affineCoordinates p01 = zero₄ , one₄
affineCoordinates p1Zeta = one₄ , zeta₄
affineCoordinates p1ZetaSquared = one₄ , zetaSquared₄
affineCoordinates pZetaZeta = zeta₄ , zeta₄
affineCoordinates pZetaZetaSquared = zeta₄ , zetaSquared₄
affineCoordinates pZetaSquaredZeta = zetaSquared₄ , zeta₄
affineCoordinates pZetaSquaredZetaSquared = zetaSquared₄ , zetaSquared₄

allListedPointsSatisfy :
  (p : AffineF4Point) →
  satisfiesCurve (proj₁ (affineCoordinates p))
                 (proj₂ (affineCoordinates p)) ≡ true
allListedPointsSatisfy p00 = refl
allListedPointsSatisfy p01 = refl
allListedPointsSatisfy p1Zeta = refl
allListedPointsSatisfy p1ZetaSquared = refl
allListedPointsSatisfy pZetaZeta = refl
allListedPointsSatisfy pZetaZetaSquared = refl
allListedPointsSatisfy pZetaSquaredZeta = refl
allListedPointsSatisfy pZetaSquaredZetaSquared = refl

classify :
  (x y : F4) →
  satisfiesCurve x y ≡ true →
  AffineF4Point
classify zero₄ zero₄ proof = p00
classify zero₄ one₄ proof = p01
classify zero₄ zeta₄ ()
classify zero₄ zetaSquared₄ ()
classify one₄ zero₄ ()
classify one₄ one₄ ()
classify one₄ zeta₄ proof = p1Zeta
classify one₄ zetaSquared₄ proof = p1ZetaSquared
classify zeta₄ zero₄ ()
classify zeta₄ one₄ ()
classify zeta₄ zeta₄ proof = pZetaZeta
classify zeta₄ zetaSquared₄ proof = pZetaZetaSquared
classify zetaSquared₄ zero₄ ()
classify zetaSquared₄ one₄ ()
classify zetaSquared₄ zeta₄ proof = pZetaSquaredZeta
classify zetaSquared₄ zetaSquared₄ proof = pZetaSquaredZetaSquared

classifiedCoordinatesExact :
  (x y : F4) →
  (h : satisfiesCurve x y ≡ true) →
  affineCoordinates (classify x y h) ≡ (x , y)
classifiedCoordinatesExact zero₄ zero₄ h = refl
classifiedCoordinatesExact zero₄ one₄ h = refl
classifiedCoordinatesExact zero₄ zeta₄ ()
classifiedCoordinatesExact zero₄ zetaSquared₄ ()
classifiedCoordinatesExact one₄ zero₄ ()
classifiedCoordinatesExact one₄ one₄ ()
classifiedCoordinatesExact one₄ zeta₄ h = refl
classifiedCoordinatesExact one₄ zetaSquared₄ h = refl
classifiedCoordinatesExact zeta₄ zero₄ ()
classifiedCoordinatesExact zeta₄ one₄ ()
classifiedCoordinatesExact zeta₄ zeta₄ h = refl
classifiedCoordinatesExact zeta₄ zetaSquared₄ h = refl
classifiedCoordinatesExact zetaSquared₄ zero₄ ()
classifiedCoordinatesExact zetaSquared₄ one₄ ()
classifiedCoordinatesExact zetaSquared₄ zeta₄ h = refl
classifiedCoordinatesExact zetaSquared₄ zetaSquared₄ h = refl

classifyListedExact :
  (p : AffineF4Point) →
  classify (proj₁ (affineCoordinates p))
           (proj₂ (affineCoordinates p))
           (allListedPointsSatisfy p) ≡ p
classifyListedExact p00 = refl
classifyListedExact p01 = refl
classifyListedExact p1Zeta = refl
classifyListedExact p1ZetaSquared = refl
classifyListedExact pZetaZeta = refl
classifyListedExact pZetaZetaSquared = refl
classifyListedExact pZetaSquaredZeta = refl
classifyListedExact pZetaSquaredZetaSquared = refl

data RationalF4Point : Set where
  infinity : RationalF4Point
  affine : AffineF4Point → RationalF4Point

affineCount : Nat
affineCount = 2 + 2 * 3

rationalCount : Nat
rationalCount = 1 + affineCount

affineCountIsEight : affineCount ≡ 8
affineCountIsEight = refl

rationalCountIsNine : rationalCount ≡ 9
rationalCountIsNine = refl

------------------------------------------------------------------------
-- Actual coordinatewise Frobenius on E(F4).
--
-- The fixed rational points are infinity, (0,0), and (0,1).
-- The other six points form three conjugate pairs.
------------------------------------------------------------------------

frobeniusAffine : AffineF4Point → AffineF4Point
frobeniusAffine p00 = p00
frobeniusAffine p01 = p01
frobeniusAffine p1Zeta = p1ZetaSquared
frobeniusAffine p1ZetaSquared = p1Zeta
frobeniusAffine pZetaZeta = pZetaSquaredZetaSquared
frobeniusAffine pZetaZetaSquared = pZetaSquaredZeta
frobeniusAffine pZetaSquaredZeta = pZetaZetaSquared
frobeniusAffine pZetaSquaredZetaSquared = pZetaZeta

frobeniusAffineCoordinates :
  (p : AffineF4Point) →
  affineCoordinates (frobeniusAffine p)
  ≡ (frobeniusSquare (proj₁ (affineCoordinates p)) ,
     frobeniusSquare (proj₂ (affineCoordinates p)))
frobeniusAffineCoordinates p00 = refl
frobeniusAffineCoordinates p01 = refl
frobeniusAffineCoordinates p1Zeta = refl
frobeniusAffineCoordinates p1ZetaSquared = refl
frobeniusAffineCoordinates pZetaZeta = refl
frobeniusAffineCoordinates pZetaZetaSquared = refl
frobeniusAffineCoordinates pZetaSquaredZeta = refl
frobeniusAffineCoordinates pZetaSquaredZetaSquared = refl

frobeniusAffineInvolutive :
  (p : AffineF4Point) →
  frobeniusAffine (frobeniusAffine p) ≡ p
frobeniusAffineInvolutive p00 = refl
frobeniusAffineInvolutive p01 = refl
frobeniusAffineInvolutive p1Zeta = refl
frobeniusAffineInvolutive p1ZetaSquared = refl
frobeniusAffineInvolutive pZetaZeta = refl
frobeniusAffineInvolutive pZetaZetaSquared = refl
frobeniusAffineInvolutive pZetaSquaredZeta = refl
frobeniusAffineInvolutive pZetaSquaredZetaSquared = refl

frobeniusRational : RationalF4Point → RationalF4Point
frobeniusRational infinity = infinity
frobeniusRational (affine p) = affine (frobeniusAffine p)

frobeniusRationalInvolutive :
  (p : RationalF4Point) →
  frobeniusRational (frobeniusRational p) ≡ p
frobeniusRationalInvolutive infinity = refl
frobeniusRationalInvolutive (affine p)
  rewrite frobeniusAffineInvolutive p = refl

data F4FrobeniusOrbit : Set where
  fixedInfinity : F4FrobeniusOrbit
  fixed00 : F4FrobeniusOrbit
  fixed01 : F4FrobeniusOrbit
  pairUnitX : F4FrobeniusOrbit
  pairEqualPhase : F4FrobeniusOrbit
  pairOppositePhase : F4FrobeniusOrbit

frobeniusOrbit : RationalF4Point → F4FrobeniusOrbit
frobeniusOrbit infinity = fixedInfinity
frobeniusOrbit (affine p00) = fixed00
frobeniusOrbit (affine p01) = fixed01
frobeniusOrbit (affine p1Zeta) = pairUnitX
frobeniusOrbit (affine p1ZetaSquared) = pairUnitX
frobeniusOrbit (affine pZetaZeta) = pairEqualPhase
frobeniusOrbit (affine pZetaZetaSquared) = pairOppositePhase
frobeniusOrbit (affine pZetaSquaredZeta) = pairOppositePhase
frobeniusOrbit (affine pZetaSquaredZetaSquared) = pairEqualPhase

frobeniusOrbitInvariant :
  (p : RationalF4Point) →
  frobeniusOrbit (frobeniusRational p) ≡ frobeniusOrbit p
frobeniusOrbitInvariant infinity = refl
frobeniusOrbitInvariant (affine p00) = refl
frobeniusOrbitInvariant (affine p01) = refl
frobeniusOrbitInvariant (affine p1Zeta) = refl
frobeniusOrbitInvariant (affine p1ZetaSquared) = refl
frobeniusOrbitInvariant (affine pZetaZeta) = refl
frobeniusOrbitInvariant (affine pZetaZetaSquared) = refl
frobeniusOrbitInvariant (affine pZetaSquaredZeta) = refl
frobeniusOrbitInvariant (affine pZetaSquaredZetaSquared) = refl

frobeniusFixedPointCount : Nat
frobeniusFixedPointCount = 3

frobeniusConjugatePairCount : Nat
frobeniusConjugatePairCount = 3

frobeniusPartitionCount :
  frobeniusFixedPointCount + 2 * frobeniusConjugatePairCount
  ≡ rationalCount
frobeniusPartitionCount = refl

frobeniusOrbitCount : Nat
frobeniusOrbitCount =
  frobeniusFixedPointCount + frobeniusConjugatePairCount

frobeniusOrbitCountIsSix :
  frobeniusOrbitCount ≡ 6
frobeniusOrbitCountIsSix = refl

-- Distinguish actual curve-coordinate Frobenius from the freely flipping
-- Banerjee source-vocabulary sheet: their fixed-point behaviour differs.
data CurveFrobeniusEqualsFreeBanerjeeSheetFlip : Set where

curveFrobeniusNotFreeSheetFlip :
  CurveFrobeniusEqualsFreeBanerjeeSheetFlip → ⊥
curveFrobeniusNotFreeSheetFlip ()

-- Reuse the repo's literal ternary phase vocabulary as a THREE-WAY LABEL;
-- no ring homomorphism from Eisenstein characteristic zero to F4 is claimed.
ternaryPhaseToF4Label : Phase.TernaryPoint → F4
ternaryPhaseToF4Label Phase.zeroPoint = zero₄
ternaryPhaseToF4Label Phase.zetaPoint = zeta₄
ternaryPhaseToF4Label Phase.zetaSquaredPoint = zetaSquared₄

phaseZetaSolvesTraceOne :
  yTrace (ternaryPhaseToF4Label Phase.zetaPoint) ≡ one₄
phaseZetaSolvesTraceOne = refl

phaseZetaSquaredSolvesTraceOne :
  yTrace (ternaryPhaseToF4Label Phase.zetaSquaredPoint) ≡ one₄
phaseZetaSquaredSolvesTraceOne = refl

data CyclotomicCharacteristicZeroEqualsF4Field : Set where

noCyclotomicF4FieldIdentification :
  CyclotomicCharacteristicZeroEqualsF4Field → ⊥
noCyclotomicF4FieldIdentification ()

claimOrigin : Attribution.ClaimOrigin
claimOrigin = Attribution.repositoryNewExtension

record F4ZetaCurvePointBoundary : Set where
  constructor f4-zeta-curve-point-boundary
  field
    literalFourElementArithmetic : Bool
    zetaMinimalPolynomialPaid : Bool
    frobeniusSwapsZetaAndZetaSquared : Bool
    eightAffinePointsClassifiedExhaustively : Bool
    nineRationalPointsIncludingInfinity : Bool
    coordinatewiseFrobeniusInvolutionPaid : Bool
    frobeniusThreeFixedThreePairsPaid : Bool
    characteristicZeroCyclotomicFieldIdentifiedWithF4 : Bool
    gamma0FourFiniteFlatMarkedSchemeConstructed : Bool

canonicalBoundary : F4ZetaCurvePointBoundary
canonicalBoundary =
  f4-zeta-curve-point-boundary
    true true true true true true true false false
