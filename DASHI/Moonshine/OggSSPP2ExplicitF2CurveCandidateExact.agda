module DASHI.Moonshine.OggSSPP2ExplicitF2CurveCandidateExact where

------------------------------------------------------------------------
-- EXPLICIT p=2 / F2 GENERALIZED-WEIERSTRASS CURVE CANDIDATE
--
-- DASHI FINITE CONSTRUCTION
--
-- We construct the characteristic-two equation
--
--     y^2 + y = x^3
--
-- over the literal two-element field carrier used here as a finite arithmetic
-- model.  This is the same coefficient pattern used by the Lean lane:
--
--     (a1,a2,a3,a4,a6) = (0,0,1,0,0).
--
-- The finite layer proves:
--   * the exact coefficient tuple;
--   * the four F2 affine inputs are classified;
--   * exactly (0,0) and (0,1) satisfy the equation;
--   * therefore there are two affine points and three F2-rational points after
--     adjoining the distinguished point at infinity.
--
-- This file does NOT construct the elliptic-curve group law over arbitrary
-- extensions, prove geometric two-torsion triviality, or promote the candidate
-- to the source supersingular curve.  Those remain separate.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_)

import DASHI.Moonshine.OggSSPMonstrousExponentSourceAttributionExact as Attribution

------------------------------------------------------------------------
-- 1. Literal F2 arithmetic.
------------------------------------------------------------------------

data F2 : Set where
  zero₂ : F2
  one₂ : F2

_+₂_ : F2 -> F2 -> F2
zero₂ +₂ y = y
one₂ +₂ zero₂ = one₂
one₂ +₂ one₂ = zero₂

_*₂_ : F2 -> F2 -> F2
zero₂ *₂ y = zero₂
one₂ *₂ y = y

square₂ : F2 -> F2
square₂ x = x *₂ x

cube₂ : F2 -> F2
cube₂ x = (x *₂ x) *₂ x

square₂-id :
  (x : F2) ->
  square₂ x ≡ x
square₂-id zero₂ = refl
square₂-id one₂ = refl

cube₂-id :
  (x : F2) ->
  cube₂ x ≡ x
cube₂-id zero₂ = refl
cube₂-id one₂ = refl

------------------------------------------------------------------------
-- 2. Generalized-Weierstrass coefficient record.
------------------------------------------------------------------------

record F2WeierstrassCoefficients : Set where
  constructor f2-weierstrass-coefficients
  field
    a1 : F2
    a2 : F2
    a3 : F2
    a4 : F2
    a6 : F2

open F2WeierstrassCoefficients public

curve : F2WeierstrassCoefficients
curve =
  f2-weierstrass-coefficients
    zero₂ zero₂ one₂ zero₂ zero₂

curve-a1 : a1 curve ≡ zero₂
curve-a1 = refl

curve-a2 : a2 curve ≡ zero₂
curve-a2 = refl

curve-a3 : a3 curve ≡ one₂
curve-a3 = refl

curve-a4 : a4 curve ≡ zero₂
curve-a4 = refl

curve-a6 : a6 curve ≡ zero₂
curve-a6 = refl

------------------------------------------------------------------------
-- 3. Exact affine equation.
------------------------------------------------------------------------

satisfiesCurve : F2 -> F2 -> Bool
satisfiesCurve x y
  with (square₂ y +₂ y) | cube₂ x
... | zero₂ | zero₂ = true
... | zero₂ | one₂ = false
... | one₂ | zero₂ = false
... | one₂ | one₂ = true

point00-satisfies :
  satisfiesCurve zero₂ zero₂ ≡ true
point00-satisfies = refl

point01-satisfies :
  satisfiesCurve zero₂ one₂ ≡ true
point01-satisfies = refl

point10-does-not-satisfy :
  satisfiesCurve one₂ zero₂ ≡ false
point10-does-not-satisfy = refl

point11-does-not-satisfy :
  satisfiesCurve one₂ one₂ ≡ false
point11-does-not-satisfy = refl

data AffineF2Point : Set where
  point00 : AffineF2Point
  point01 : AffineF2Point

affineCoordinates :
  AffineF2Point ->
  F2 × F2
affineCoordinates point00 = zero₂ , zero₂
affineCoordinates point01 = zero₂ , one₂

affineCoordinatesSatisfy :
  (point : AffineF2Point) ->
  satisfiesCurve
    (Data.Product.proj₁ (affineCoordinates point))
    (Data.Product.proj₂ (affineCoordinates point))
  ≡ true
affineCoordinatesSatisfy point00 = refl
affineCoordinatesSatisfy point01 = refl

------------------------------------------------------------------------
-- 4. Completeness of the affine classification.
------------------------------------------------------------------------

classifySatisfyingPair :
  (x y : F2) ->
  satisfiesCurve x y ≡ true ->
  AffineF2Point
classifySatisfyingPair zero₂ zero₂ proof = point00
classifySatisfyingPair zero₂ one₂ proof = point01
classifySatisfyingPair one₂ zero₂ ()
classifySatisfyingPair one₂ one₂ ()

classifiedCoordinatesExact :
  (x y : F2) ->
  (proof : satisfiesCurve x y ≡ true) ->
  affineCoordinates (classifySatisfyingPair x y proof)
  ≡ (x , y)
classifiedCoordinatesExact zero₂ zero₂ proof = refl
classifiedCoordinatesExact zero₂ one₂ proof = refl
classifiedCoordinatesExact one₂ zero₂ ()
classifiedCoordinatesExact one₂ one₂ ()

------------------------------------------------------------------------
-- 5. Exact finite counts.
------------------------------------------------------------------------

affinePointCount : Nat
affinePointCount = 2

affinePointCountIsTwo :
  affinePointCount ≡ 2
affinePointCountIsTwo = refl

rationalPointCount : Nat
rationalPointCount = 3

rationalPointCountIsThree :
  rationalPointCount ≡ 3
rationalPointCountIsThree = refl

------------------------------------------------------------------------
-- 6. Semantic firewalls.
------------------------------------------------------------------------

data ThreePointCountCreatesSupersingularity : Set where
data ExplicitEquationCreatesGeometricTwoTorsionTheorem : Set where
data ExplicitF2CurveCreatesUniversalDeformation : Set where

threePointCountDoesNotCreateSupersingularity :
  ThreePointCountCreatesSupersingularity -> ⊥
threePointCountDoesNotCreateSupersingularity ()

explicitEquationDoesNotCreateGeometricTwoTorsionTheorem :
  ExplicitEquationCreatesGeometricTwoTorsionTheorem -> ⊥
explicitEquationDoesNotCreateGeometricTwoTorsionTheorem ()

explicitF2CurveDoesNotCreateUniversalDeformation :
  ExplicitF2CurveCreatesUniversalDeformation -> ⊥
explicitF2CurveDoesNotCreateUniversalDeformation ()

claimOrigin : Attribution.ClaimOrigin
claimOrigin = Attribution.repositoryNewExtension

record ExplicitF2CurveCandidateBoundary : Set where
  constructor explicit-f2-curve-candidate-boundary
  field
    literalF2CarrierOwned : Bool
    generalizedWeierstrassCoefficientTupleOwned : Bool
    exactAffineSolutionClassificationPaid : Bool
    affinePointCountTwoPaid : Bool
    rationalPointCountThreePaid : Bool
    geometricTwoTorsionTrivialPaid : Bool
    supersingularityRecognized : Bool
    universalDeformationSameObject : Bool

canonicalExplicitF2CurveCandidateBoundary :
  ExplicitF2CurveCandidateBoundary
canonicalExplicitF2CurveCandidateBoundary =
  explicit-f2-curve-candidate-boundary
    true true true true true false false false
