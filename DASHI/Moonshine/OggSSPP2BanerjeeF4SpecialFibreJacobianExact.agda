module DASHI.Moonshine.OggSSPP2BanerjeeF4SpecialFibreJacobianExact where

------------------------------------------------------------------------
-- BANERJEE'S ACTUAL CHARACTERISTIC-2 SPECIAL FIBRE
--
-- EXTERNAL: Romie Banerjee, "A modular description of ER(2)",
-- New York Journal of Mathematics 20 (2014), 743--758,
-- Section 3.1, Proposition 3.1 and the universal curve following it:
--
--   C/F4 : y^2 + y = x^3
--   C~ / W(F4)[[a1]] : y^2 + a1*x*y + y = x^3.
--
-- Banerjee's further explicit level structure concerns Gamma_0(3), not
-- Gamma_0(4).  A Gamma_0(4) flag on C~ is a SEPARATE geometric obligation.
--
-- DASHI: build the finite F4-point solution set and its elementary
-- characteristic-2 Jacobian witnesses, with an exact eight-point affine
-- classification.  This is NOT a construction of W(F4), its power-series
-- scheme, the finite-flat Frobenius kernels, or an integral 2B module.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_)

import DASHI.Moonshine.OggSSPP2BanerjeeF4UniversalDeformationSourceExact as Banerjee
import DASHI.Moonshine.OggSSPMonstrousExponentSourceAttributionExact as Attribution

------------------------------------------------------------------------
-- 1. The four-element residue field presented by 0,1,alpha,alpha+1.
--    In F4, alpha^2=alpha+1, alpha^3=1 and alpha^2+alpha=1.
------------------------------------------------------------------------

data F4Coordinate : Set where
  zero fourOne alpha alphaPlusOne : F4Coordinate

squareF4 : F4Coordinate -> F4Coordinate
squareF4 zero = zero
squareF4 fourOne = fourOne
squareF4 alpha = alphaPlusOne
squareF4 alphaPlusOne = alpha

cubeF4 : F4Coordinate -> F4Coordinate
cubeF4 zero = zero
cubeF4 fourOne = fourOne
cubeF4 alpha = fourOne
cubeF4 alphaPlusOne = fourOne

artinSchreierF4 : F4Coordinate -> F4Coordinate
artinSchreierF4 zero = zero
artinSchreierF4 fourOne = zero
artinSchreierF4 alpha = fourOne
artinSchreierF4 alphaPlusOne = fourOne

-- The affine special-fibre equation y^2+y=x^3.
OnBanerjeeSpecialFibre :
  F4Coordinate -> F4Coordinate -> Set
OnBanerjeeSpecialFibre x y =
  artinSchreierF4 y ≡ cubeF4 x

------------------------------------------------------------------------
-- 2. All F4-rational affine points, not just a count annotation.
------------------------------------------------------------------------

data AffineSolution : F4Coordinate -> F4Coordinate -> Set where
  atZeroZero : AffineSolution zero zero
  atZeroOne : AffineSolution zero fourOne
  atOneAlpha : AffineSolution fourOne alpha
  atOneAlphaPlusOne : AffineSolution fourOne alphaPlusOne
  atAlphaAlpha : AffineSolution alpha alpha
  atAlphaAlphaPlusOne : AffineSolution alpha alphaPlusOne
  atAlphaPlusOneAlpha : AffineSolution alphaPlusOne alpha
  atAlphaPlusOneAlphaPlusOne : AffineSolution alphaPlusOne alphaPlusOne

solutionSatisfiesEquation :
  {x y : F4Coordinate} ->
  AffineSolution x y -> OnBanerjeeSpecialFibre x y
solutionSatisfiesEquation atZeroZero = refl
solutionSatisfiesEquation atZeroOne = refl
solutionSatisfiesEquation atOneAlpha = refl
solutionSatisfiesEquation atOneAlphaPlusOne = refl
solutionSatisfiesEquation atAlphaAlpha = refl
solutionSatisfiesEquation atAlphaAlphaPlusOne = refl
solutionSatisfiesEquation atAlphaPlusOneAlpha = refl
solutionSatisfiesEquation atAlphaPlusOneAlphaPlusOne = refl

everyF4AffinePointIsListed :
  (x y : F4Coordinate) ->
  OnBanerjeeSpecialFibre x y ->
  AffineSolution x y
everyF4AffinePointIsListed zero zero _ = atZeroZero
everyF4AffinePointIsListed zero fourOne _ = atZeroOne
everyF4AffinePointIsListed zero alpha ()
everyF4AffinePointIsListed zero alphaPlusOne ()
everyF4AffinePointIsListed fourOne zero ()
everyF4AffinePointIsListed fourOne fourOne ()
everyF4AffinePointIsListed fourOne alpha _ = atOneAlpha
everyF4AffinePointIsListed fourOne alphaPlusOne _ = atOneAlphaPlusOne
everyF4AffinePointIsListed alpha zero ()
everyF4AffinePointIsListed alpha fourOne ()
everyF4AffinePointIsListed alpha alpha _ = atAlphaAlpha
everyF4AffinePointIsListed alpha alphaPlusOne _ = atAlphaAlphaPlusOne
everyF4AffinePointIsListed alphaPlusOne zero ()
everyF4AffinePointIsListed alphaPlusOne fourOne ()
everyF4AffinePointIsListed alphaPlusOne alpha _ = atAlphaPlusOneAlpha
everyF4AffinePointIsListed alphaPlusOne alphaPlusOne _ =
  atAlphaPlusOneAlphaPlusOne

------------------------------------------------------------------------
-- 3. Exact finite coordinate Jacobian of the special fibre.
--
-- f(x,y)=y^2+y-x^3; in characteristic 2, its formal partial derivative
-- d(f)/dy = 2y+1 = 1.  Hence no affine geometric point is singular.
-- The function below presents that DERIVATIVE, not a general-purpose
-- differential-polynomial or smooth-scheme development.
------------------------------------------------------------------------

affinePartialY :
  F4Coordinate -> F4Coordinate -> F4Coordinate
affinePartialY x y = fourOne

affinePartialYIsUnit :
  (x y : F4Coordinate) ->
  affinePartialY x y ≡ fourOne
affinePartialYIsUnit x y = refl

data AffineJacobianYVanishes : Set where
  affineJacobianYVanishes :
    (x y : F4Coordinate) ->
    OnBanerjeeSpecialFibre x y ->
    affinePartialY x y ≡ zero ->
    AffineJacobianYVanishes

noAffineF4JacobianSingularity :
  AffineJacobianYVanishes -> ⊥
noAffineF4JacobianSingularity
  (affineJacobianYVanishes x y equation ())

------------------------------------------------------------------------
-- 4. The formal/projective infinity chart has the unique infinity point
--    [0:1:0]. The derivative of
--
--      Y^2 Z + Y Z^2 - X^3
--
--    with respect to Z is Y^2 in characteristic 2 at Z=0, hence 1
--    at the normalized infinity point. This is a selected chart check,
--    not a construction of the projective curve as a scheme.
------------------------------------------------------------------------

data ProjectiveInfinityChart : Set where
  normalizedInfinity : ProjectiveInfinityChart

infinityPartialZ : ProjectiveInfinityChart -> F4Coordinate
infinityPartialZ normalizedInfinity = fourOne

infinityPartialZIsUnit :
  (point : ProjectiveInfinityChart) ->
  infinityPartialZ point ≡ fourOne
infinityPartialZIsUnit normalizedInfinity = refl

------------------------------------------------------------------------
-- 5. Exact level attribution boundary: Banerjee's level 3 != level 4.
------------------------------------------------------------------------

data ModularLevel : Set where
  gammaZeroThree gammaZeroFour : ModularLevel

banerjeeExplicitLevel : ModularLevel
banerjeeExplicitLevel = gammaZeroThree

proposedBadPrimeAttachmentLevel : ModularLevel
proposedBadPrimeAttachmentLevel = gammaZeroFour

banerjeeLevelDoesNotIdentifyGammaZeroFour :
  banerjeeExplicitLevel ≡ proposedBadPrimeAttachmentLevel -> ⊥
banerjeeLevelDoesNotIdentifyGammaZeroFour ()

banerjeePrimarySource :
  Banerjee.BanerjeeF4UniversalDeformationReceipt
banerjeePrimarySource =
  Banerjee.canonicalBanerjeeF4UniversalDeformationReceipt

data SpecialFibrePointCheckBuildsWittEllipticScheme : Set where
data GammaZeroThreeLevelBuildsGammaZeroFourFlag : Set where
data FiniteF4PointsBuildActualTwoBTateModule : Set where

finitePointCheckDoesNotBuildWittScheme :
  SpecialFibrePointCheckBuildsWittEllipticScheme -> ⊥
finitePointCheckDoesNotBuildWittScheme ()

gammaZeroThreeDoesNotBuildGammaZeroFour :
  GammaZeroThreeLevelBuildsGammaZeroFourFlag -> ⊥
gammaZeroThreeDoesNotBuildGammaZeroFour ()

finiteF4CurveDoesNotBuildIntegralTwoBModule :
  FiniteF4PointsBuildActualTwoBTateModule -> ⊥
finiteF4CurveDoesNotBuildIntegralTwoBModule ()

claimOrigin : Attribution.ClaimOrigin
claimOrigin = Attribution.repositoryFormalReconstruction

record BanerjeeF4SpecialFibreJacobianBoundary : Set where
  constructor banerjee-f4-special-fibre-jacobian-boundary
  field
    actualBanerjeeF4EquationUsed : Bool
    eightAffineF4SolutionsExplicit : Bool
    finiteF4AffineClassificationExhaustive : Bool
    affineJacobianYNonzero : Bool
    projectiveInfinityChartJacobianNonzero : Bool
    banerjeeLevelThreeDistinguishedFromGammaZeroFour : Bool
    wittSchemeConstructedHere : Bool
    rankFourFiniteFlatFlagConstructedHere : Bool
    actualTwoBIntegralModuleConstructedHere : Bool

canonicalBanerjeeF4SpecialFibreJacobianBoundary :
  BanerjeeF4SpecialFibreJacobianBoundary
canonicalBanerjeeF4SpecialFibreJacobianBoundary =
  banerjee-f4-special-fibre-jacobian-boundary
    true true true true true true false false false
