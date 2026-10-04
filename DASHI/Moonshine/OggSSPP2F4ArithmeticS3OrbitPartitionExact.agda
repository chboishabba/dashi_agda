module DASHI.Moonshine.OggSSPP2F4ArithmeticS3OrbitPartitionExact where

------------------------------------------------------------------------
-- ARITHMETIC S3 ORBITS OF THE ACTUAL FINITE F4 CURVE
--
-- Not a count-only 369 quotient. The actual source coordinate maps
--   F(x,y)=(x²,y²), rho(x,y)=(zeta*x,y)
-- generate the following partition on E(F4):
--
--   {infinity}, {(0,0)}, {(0,1)}, {six nonzero-x affine points}.
--
-- The six-point component is an actual orbit: it is explicitly reached
-- from Q=(1,zeta) using rho^i and F rho^i.
-- This source-native profile is 1+1+1+6, i.e. four S3 orbits.
--
-- No source Monster orbit or full elliptic/VOA intertwiner is inferred.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
import DASHI.Moonshine.OggSSPP2F4ZetaCurvePointEnumerationExact as Curve
import DASHI.Moonshine.OggSSPP2F4EllipticS3NineSheetBidiExact as Eigen
import DASHI.Moonshine.OggSSPP2F4RecenteredTriXorS3Exact as Plane

data S3OrbitClass : Set where
  infinitySingleton : S3OrbitClass
  pSingleton : S3OrbitClass
  minusPSingleton : S3OrbitClass
  sixPointOrbit : S3OrbitClass

sourceClass : Curve.RationalF4Point → S3OrbitClass
sourceClass Curve.infinity = infinitySingleton
sourceClass (Curve.affine Curve.p00) = pSingleton
sourceClass (Curve.affine Curve.p01) = minusPSingleton
sourceClass (Curve.affine Curve.p1Zeta) = sixPointOrbit
sourceClass (Curve.affine Curve.pZetaZeta) = sixPointOrbit
sourceClass (Curve.affine Curve.pZetaSquaredZeta) = sixPointOrbit
sourceClass (Curve.affine Curve.p1ZetaSquared) = sixPointOrbit
sourceClass (Curve.affine Curve.pZetaZetaSquared) = sixPointOrbit
sourceClass (Curve.affine Curve.pZetaSquaredZetaSquared) = sixPointOrbit

sourceClassFrobeniusInvariant :
  (p : Curve.RationalF4Point) →
  sourceClass (Curve.frobeniusRational p) ≡ sourceClass p
sourceClassFrobeniusInvariant (Curve.infinity) = refl
sourceClassFrobeniusInvariant (Curve.affine Curve.p00) = refl
sourceClassFrobeniusInvariant (Curve.affine Curve.p01) = refl
sourceClassFrobeniusInvariant (Curve.affine Curve.p1Zeta) = refl
sourceClassFrobeniusInvariant (Curve.affine Curve.p1ZetaSquared) = refl
sourceClassFrobeniusInvariant (Curve.affine Curve.pZetaZeta) = refl
sourceClassFrobeniusInvariant (Curve.affine Curve.pZetaZetaSquared) = refl
sourceClassFrobeniusInvariant (Curve.affine Curve.pZetaSquaredZeta) = refl
sourceClassFrobeniusInvariant (Curve.affine Curve.pZetaSquaredZetaSquared) = refl

sourceClassShearInvariant :
  (p : Curve.RationalF4Point) →
  sourceClass (Eigen.rhoCurve p) ≡ sourceClass p
sourceClassShearInvariant (Curve.infinity) = refl
sourceClassShearInvariant (Curve.affine Curve.p00) = refl
sourceClassShearInvariant (Curve.affine Curve.p01) = refl
sourceClassShearInvariant (Curve.affine Curve.p1Zeta) = refl
sourceClassShearInvariant (Curve.affine Curve.p1ZetaSquared) = refl
sourceClassShearInvariant (Curve.affine Curve.pZetaZeta) = refl
sourceClassShearInvariant (Curve.affine Curve.pZetaZetaSquared) = refl
sourceClassShearInvariant (Curve.affine Curve.pZetaSquaredZeta) = refl
sourceClassShearInvariant (Curve.affine Curve.pZetaSquaredZetaSquared) = refl

-- The six mobile points are exactly Q and its five S3 translates.
Q : Curve.RationalF4Point
Q = Curve.affine Curve.p1Zeta

data S3Word6 : Set where
  identityWord : S3Word6
  rhoWord : S3Word6
  rhoSquaredWord : S3Word6
  frobeniusWord : S3Word6
  rhoFrobeniusWord : S3Word6
  rhoSquaredFrobeniusWord : S3Word6

applyS3Word : S3Word6 → Curve.RationalF4Point
applyS3Word identityWord = Q
applyS3Word rhoWord = Eigen.rhoCurve Q
applyS3Word rhoSquaredWord = Eigen.rhoCurve (Eigen.rhoCurve Q)
applyS3Word frobeniusWord = Curve.frobeniusRational Q
applyS3Word rhoFrobeniusWord =
  Eigen.rhoCurve (Curve.frobeniusRational Q)
applyS3Word rhoSquaredFrobeniusWord =
  Eigen.rhoCurve (Eigen.rhoCurve (Curve.frobeniusRational Q))

sixWordsHitDistinctSourcePoints :
  applyS3Word identityWord ≡ Curve.affine Curve.p1Zeta
  -- Remaining five are separate exact equalities below.
sixWordsHitDistinctSourcePoints = refl

rhoQIsZetaZeta :
  applyS3Word rhoWord ≡ Curve.affine Curve.pZetaZeta
rhoQIsZetaZeta = refl

rhoSquaredQIsZetaSquaredZeta :
  applyS3Word rhoSquaredWord ≡ Curve.affine Curve.pZetaSquaredZeta
rhoSquaredQIsZetaSquaredZeta = refl

frobeniusQIsOneZetaSquared :
  applyS3Word frobeniusWord ≡ Curve.affine Curve.p1ZetaSquared
frobeniusQIsOneZetaSquared = refl

rhoFrobeniusQIsZetaZetaSquared :
  applyS3Word rhoFrobeniusWord ≡ Curve.affine Curve.pZetaZetaSquared
rhoFrobeniusQIsZetaZetaSquared = refl

rhoSquaredFrobeniusQIsZetaSquaredZetaSquared :
  applyS3Word rhoSquaredFrobeniusWord
  ≡ Curve.affine Curve.pZetaSquaredZetaSquared
rhoSquaredFrobeniusQIsZetaSquaredZetaSquared = refl

mobileIsWordImage :
  (p : Curve.RationalF4Point) →
  sourceClass p ≡ sixPointOrbit →
  S3Word6
mobileIsWordImage Curve.infinity ()
mobileIsWordImage (Curve.affine Curve.p00) ()
mobileIsWordImage (Curve.affine Curve.p01) ()
mobileIsWordImage (Curve.affine Curve.p1Zeta) _ = identityWord
mobileIsWordImage (Curve.affine Curve.pZetaZeta) _ = rhoWord
mobileIsWordImage (Curve.affine Curve.pZetaSquaredZeta) _ = rhoSquaredWord
mobileIsWordImage (Curve.affine Curve.p1ZetaSquared) _ = frobeniusWord
mobileIsWordImage (Curve.affine Curve.pZetaZetaSquared) _ = rhoFrobeniusWord
mobileIsWordImage (Curve.affine Curve.pZetaSquaredZetaSquared) _ =
  rhoSquaredFrobeniusWord

mobileWordReopens :
  (p : Curve.RationalF4Point) →
  (h : sourceClass p ≡ sixPointOrbit) →
  applyS3Word (mobileIsWordImage p h) ≡ p
mobileWordReopens Curve.infinity ()
mobileWordReopens (Curve.affine Curve.p00) ()
mobileWordReopens (Curve.affine Curve.p01) ()
mobileWordReopens (Curve.affine Curve.p1Zeta) _ = refl
mobileWordReopens (Curve.affine Curve.pZetaZeta) _ = refl
mobileWordReopens (Curve.affine Curve.pZetaSquaredZeta) _ = refl
mobileWordReopens (Curve.affine Curve.p1ZetaSquared) _ = refl
mobileWordReopens (Curve.affine Curve.pZetaZetaSquared) _ = refl
mobileWordReopens (Curve.affine Curve.pZetaSquaredZetaSquared) _ = refl

-- The chosen explicit eigenchart transports the *same* four classes.
targetClass : Plane.CenteredNine → S3OrbitClass
targetClass p = sourceClass (Eigen.eigenPlaneToCurve p)

classificationIntertwinesEigenChart :
  (p : Curve.RationalF4Point) →
  targetClass (Eigen.curveToEigenPlane p) ≡ sourceClass p
classificationIntertwinesEigenChart p
  rewrite Eigen.curveEigenRoundTrip p = refl

sourceClassNegationSwapsTwoFixedNoncentralClasses :
  sourceClass (Eigen.negCurve (Curve.affine Curve.p00))
    ≡ minusPSingleton
sourceClassNegationSwapsTwoFixedNoncentralClasses = refl

------------------------------------------------------------------------
-- A substantive incompatibility: the actual S3 orbit quotient is not
-- the same quotient as elliptic inversion.  Inversion swaps (0,0)
-- and (0,1), while S3 fixes them individually.  This does not depend
-- on an intentionally empty "claim" type.
------------------------------------------------------------------------

s3ClassificationDoesNotDescendThroughInversion :
  ((p : Curve.RationalF4Point) →
   sourceClass (Eigen.negCurve p) ≡ sourceClass p) →
  ⊥
s3ClassificationDoesNotDescendThroughInversion alleged =
  incompatible (alleged (Curve.affine Curve.p00))
  where
    incompatible : minusPSingleton ≡ pSingleton → ⊥
    incompatible ()

record ArithmeticS3OrbitBoundary : Set where
  constructor arithmetic-s3-orbit-boundary
  field
    sourceArithmeticFrobeniusUsed : Bool
    sourceActualZetaShearUsed : Bool
    threeDistinctFixedSingletons : Bool
    remainingSixGeneratedFromQ : Bool
    fourSourceOrbitClasses : Bool
    orbitClassesTransportAlongEigenChart : Bool
    inversionNotConflatedWithFrobenius : Bool
    substantiveInversionQuotientNoGo : Bool
    monsterActionRecognition : Bool

canonicalArithmeticS3OrbitBoundary : ArithmeticS3OrbitBoundary
canonicalArithmeticS3OrbitBoundary =
  arithmetic-s3-orbit-boundary
    true true true true true true true true false
