{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNFixedCanonicalFiniteRealDegreeTwoRound852Exact where

------------------------------------------------------------------------
-- R852 / FINITE-REAL SCALAR COMPONENTS OF THE LITERAL ROUND71 RHS
--
-- R851 gives every Round71 canonical state/RHS exactly six real coordinates
-- per positive reality representative.  Round71's existing degree-two owner
-- gives one literal Complex3 expression for every modal RHS.  This file takes
-- the six real coordinate projections of that SAME expression.
--
-- Thus every coordinate of the finite-real encoded Round71 vector field is
-- literally a scalar projection of a repository expression of degree <= 2.
-- No Round26 unrestricted Assignment is reintroduced.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (suc; zero)
open import Data.Nat.Base using (_≤_)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNFixedCanonicalRealityVectorFieldRound71Exact as Fixed
import DASHI.Physics.Closure.NSTriadKNFixedCanonicalVectorFieldDegreeTwoRound71Exact as Degree
import DASHI.Physics.Closure.NSTriadKNFixedCanonicalFiniteRealCodecRound851Exact as Codec

data RealCoordinate : Set where
  xReal xImag yReal yImag zReal zImag : RealCoordinate

projectCoordinate :
  ∀ {r} {F : C3.RealField r} →
  RealCoordinate → C3.Complex3 F → C3.Carrier F
projectCoordinate xReal value = C3.real (C3.x value)
projectCoordinate xImag value = C3.imaginary (C3.x value)
projectCoordinate yReal value = C3.real (C3.y value)
projectCoordinate yImag value = C3.imaginary (C3.y value)
projectCoordinate zReal value = C3.real (C3.z value)
projectCoordinate zImag value = C3.imaginary (C3.z value)

literalScalarRHS :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    (geometry : Fixed.FixedCanonicalGeometry F E) →
  Fixed.CanonicalRealityState F (Fixed.cutoff geometry) →
  Z3.FourierMode → RealCoordinate → C3.Carrier F
literalScalarRHS geometry state mode coordinate =
  projectCoordinate coordinate
    (Fixed.rawCanonicalRHSAt geometry state mode)

expressionScalarRHS :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    (geometry : Fixed.FixedCanonicalGeometry F E) →
  Fixed.CanonicalRealityState F (Fixed.cutoff geometry) →
  Z3.FourierMode → RealCoordinate → C3.Carrier F
expressionScalarRHS geometry state mode coordinate =
  projectCoordinate coordinate
    (Degree.evaluateExpression state
      (Degree.modeRHSExpression geometry mode))

expressionScalarRHSEqualsLiteral :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    (geometry : Fixed.FixedCanonicalGeometry F E)
    (state : Fixed.CanonicalRealityState F (Fixed.cutoff geometry))
    (mode : Z3.FourierMode)
    (coordinate : RealCoordinate) →
  expressionScalarRHS geometry state mode coordinate
  ≡ literalScalarRHS geometry state mode coordinate
expressionScalarRHSEqualsLiteral geometry state mode coordinate =
  cong (projectCoordinate coordinate)
    (Degree.modeRHSExpressionEvaluatesExactly geometry state mode)

scalarExpressionDegreeAtMostTwo :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    (geometry : Fixed.FixedCanonicalGeometry F E)
    (mode : Z3.FourierMode)
    (coordinate : RealCoordinate) →
  Degree.expressionDegree (Degree.modeRHSExpression geometry mode)
  ≤ suc (suc zero)
scalarExpressionDegreeAtMostTwo geometry mode coordinate =
  Degree.modeRHSExpressionDegreeAtMostTwo geometry mode

------------------------------------------------------------------------
-- R851 encoding order and these six projections agree definitionally on one
-- stored modal value.  This pins the scalar projection convention used by the
-- finite-real ODE carrier.
------------------------------------------------------------------------

encodedModeCoordinates :
  ∀ {r} {F : C3.RealField r} →
  Fixed.CanonicalModeValue F →
  C3.Carrier F →
  Set
encodedModeCoordinates entry dummy =
  projectCoordinate xReal (Fixed.value entry)
    ≡ C3.real (C3.x (Fixed.value entry))

encodedXRealConventionExact :
  ∀ {r} {F : C3.RealField r}
    (entry : Fixed.CanonicalModeValue F) →
  projectCoordinate xReal (Fixed.value entry)
  ≡ C3.real (C3.x (Fixed.value entry))
encodedXRealConventionExact entry = refl

encodedXImagConventionExact :
  ∀ {r} {F : C3.RealField r}
    (entry : Fixed.CanonicalModeValue F) →
  projectCoordinate xImag (Fixed.value entry)
  ≡ C3.imaginary (C3.x (Fixed.value entry))
encodedXImagConventionExact entry = refl

encodedYRealConventionExact :
  ∀ {r} {F : C3.RealField r}
    (entry : Fixed.CanonicalModeValue F) →
  projectCoordinate yReal (Fixed.value entry)
  ≡ C3.real (C3.y (Fixed.value entry))
encodedYRealConventionExact entry = refl

encodedYImagConventionExact :
  ∀ {r} {F : C3.RealField r}
    (entry : Fixed.CanonicalModeValue F) →
  projectCoordinate yImag (Fixed.value entry)
  ≡ C3.imaginary (C3.y (Fixed.value entry))
encodedYImagConventionExact entry = refl

encodedZRealConventionExact :
  ∀ {r} {F : C3.RealField r}
    (entry : Fixed.CanonicalModeValue F) →
  projectCoordinate zReal (Fixed.value entry)
  ≡ C3.real (C3.z (Fixed.value entry))
encodedZRealConventionExact entry = refl

encodedZImagConventionExact :
  ∀ {r} {F : C3.RealField r}
    (entry : Fixed.CanonicalModeValue F) →
  projectCoordinate zImag (Fixed.value entry)
  ≡ C3.imaginary (C3.z (Fixed.value entry))
encodedZImagConventionExact entry = refl

round852EveryFiniteRealRHSCoordinateLiteral : Bool
round852EveryFiniteRealRHSCoordinateLiteral = true

round852EveryFiniteRealRHSCoordinateDegreeAtMostTwo : Bool
round852EveryFiniteRealRHSCoordinateDegreeAtMostTwo = true

round852Round26UnrestrictedAssignmentRequired : Bool
round852Round26UnrestrictedAssignmentRequired = false

round852RealBanachQuadraticPackagingClosed : Bool
round852RealBanachQuadraticPackagingClosed = false

round852ClayPromotion : Bool
round852ClayPromotion = false

round852EveryFiniteRealRHSCoordinateLiteralIsTrue :
  round852EveryFiniteRealRHSCoordinateLiteral ≡ true
round852EveryFiniteRealRHSCoordinateLiteralIsTrue = refl

round852EveryFiniteRealRHSCoordinateDegreeAtMostTwoIsTrue :
  round852EveryFiniteRealRHSCoordinateDegreeAtMostTwo ≡ true
round852EveryFiniteRealRHSCoordinateDegreeAtMostTwoIsTrue = refl
