module DASHI.Physics.Closure.NSTriadKNR290HermitianG2SquaredCauchyExact where

------------------------------------------------------------------------
-- B / G2 SHARP SQUARED HERMITIAN DIFFERENCE PAYMENT
--
-- Earlier G2 recutting proved
--
--   g(X+;D) - g(X-;D) = g(X+-X-;D).
--
-- Young's inequality gives a convenient local L1-style envelope, but the
-- paired second-moment compiler wants the sharper displacement-squared shape.
-- On the exact rational C^3 carrier we can use literal Hermitian
-- Cauchy--Schwarz:
--
--   (g+ - g-)^2
--     <= ||X+ - X-||^2 ||D||^2.
--
-- Combining this with the six-real-coordinate finite path theorem gives a
-- direct G2^2 producer with no square roots and no fibre-cardinality factor.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using
  (ℚ; 0ℚ; _+_; _*_; _-_; _≤_; nonNegative)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNOrderedEuclideanL2Carrier as L2
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNRationalComplex3Separation as Separation
import DASHI.Physics.Closure.NSTriadKNRationalComplex3HermitianCauchyRound74Exact as HC
import DASHI.Physics.Closure.NSTriadKNRawCurlFibreGramRound179Exact as R179
import DASHI.Physics.Closure.NSTriadKNR571HermitianScalarizedOppositePairExact as G0
import DASHI.Physics.Closure.NSTriadKNR290HermitianG2StateDifferenceExact as G2
import DASHI.Physics.Closure.NSTriadKNR290ComplexPathDifferenceG2Exact as PathG2
import DASHI.Physics.Closure.NSTriadKNLuoFinitePathDifferenceDiffusionExact as Path

F = G0.Weld.F

realHermitianCrossIsHermitianRealPart :
  (u v : C3.Complex3 F) →
  R179.realHermitianCross u v
  ≡ C3.real (C3.hermitianPairing3 u v)
realHermitianCrossIsHermitianRealPart
    (C3.complex3
      (C3.complex ur1 ui1) (C3.complex ur2 ui2) (C3.complex ur3 ui3))
    (C3.complex3
      (C3.complex vr1 vi1) (C3.complex vr2 vi2) (C3.complex vr3 vi3)) =
  solve
    ( ur1 ∷ ui1 ∷ ur2 ∷ ui2 ∷ ur3 ∷ ui3
    ∷ vr1 ∷ vi1 ∷ vr2 ∷ vi2 ∷ vr3 ∷ vi3 ∷ [])

realHermitianCrossSquareBelowModulus :
  (u v : C3.Complex3 F) →
  R179.realHermitianCross u v * R179.realHermitianCross u v
  ≤ L2.complexModulusSquared (C3.hermitianPairing3 u v)
realHermitianCrossSquareBelowModulus u v =
  let
    pair = C3.hermitianPairing3 u v
    realPart = C3.real pair
    imagPart = C3.imaginary pair

    imagSquareNN : 0ℚ ≤ imagPart * imagPart
    imagSquareNN = Rational.squareNonnegative imagPart

    addImag :
      realPart * realPart
      ≤ realPart * realPart + imagPart * imagPart
    addImag =
      subst
        (λ lower →
          lower ≤ realPart * realPart + imagPart * imagPart)
        (ℚP.+-identityʳ (realPart * realPart))
        (ℚP.+-monoʳ-≤ (realPart * realPart) imagSquareNN)
  in
  subst
    (λ lhs → lhs ≤ L2.complexModulusSquared pair)
    (cong (λ value → value * value)
      (realHermitianCrossIsHermitianRealPart u v))
    addImag

realHermitianCrossSquaredCauchy :
  (u v : C3.Complex3 F) →
  R179.realHermitianCross u v * R179.realHermitianCross u v
  ≤
  L2.complex3NormSquared u * L2.complex3NormSquared v
realHermitianCrossSquaredCauchy u v =
  ℚP.≤-trans
    (realHermitianCrossSquareBelowModulus u v)
    (HC.rationalComplex3HermitianCauchy u v)

hermitianStateDifferenceSquaredBound :
  (XPlus XMinus D : C3.Complex3 F) →
  (G0.hermitianScalar XPlus D - G0.hermitianScalar XMinus D)
  *
  (G0.hermitianScalar XPlus D - G0.hermitianScalar XMinus D)
  ≤
  L2.complex3NormSquared (C3.complex3Subtract XPlus XMinus)
  * L2.complex3NormSquared D
hermitianStateDifferenceSquaredBound XPlus XMinus D =
  let
    exact = G2.hermitianStateDifferenceExact XPlus XMinus D
    cauchy =
      realHermitianCrossSquaredCauchy
        (C3.complex3Subtract XPlus XMinus) D
  in
  subst
    (λ lhs →
      lhs * lhs
      ≤
      L2.complex3NormSquared (C3.complex3Subtract XPlus XMinus)
      * L2.complex3NormSquared D)
    (sym exact)
    cauchy

hermitianStateDifferenceSquaredPathBound :
  (XPlus XMinus D : C3.Complex3 F) →
  (R : PathG2.ComplexPathRealization XPlus XMinus) →
  let
    pathBudget =
      Path.pathStepCount (PathG2.realPath R)
        * Path.pathGradientEnergy (PathG2.realPath R)
      +
      Path.pathStepCount (PathG2.imagPath R)
        * Path.pathGradientEnergy (PathG2.imagPath R)
  in
  (G0.hermitianScalar XPlus D - G0.hermitianScalar XMinus D)
  *
  (G0.hermitianScalar XPlus D - G0.hermitianScalar XMinus D)
  ≤
  pathBudget * L2.complex3NormSquared D
hermitianStateDifferenceSquaredPathBound XPlus XMinus D R =
  let
    base = hermitianStateDifferenceSquaredBound XPlus XMinus D
    path = PathG2.complexPathDifferenceBound XPlus XMinus R

    dNN : 0ℚ ≤ L2.complex3NormSquared D
    dNN = Separation.complex3NormSquaredNonnegative D

    scaled :
      L2.complex3NormSquared (C3.complex3Subtract XPlus XMinus)
        * L2.complex3NormSquared D
      ≤
      ( Path.pathStepCount (PathG2.realPath R)
          * Path.pathGradientEnergy (PathG2.realPath R)
        +
        Path.pathStepCount (PathG2.imagPath R)
          * Path.pathGradientEnergy (PathG2.imagPath R))
        * L2.complex3NormSquared D
    scaled =
      let
        instance
          dNNI = nonNegative dNN
      in
      ℚP.*-monoʳ-≤-nonNeg
        (L2.complex3NormSquared D) path
  in
  ℚP.≤-trans base scaled

r290HermitianG2SquaredCauchyClosed : Bool
r290HermitianG2SquaredCauchyClosed = true

r290HermitianG2PathSquaredBoundClosed : Bool
r290HermitianG2PathSquaredBoundClosed = true

squareRootIntroduced : Bool
squareRootIntroduced = false

physicalDisplacementToPathClosedHere : Bool
physicalDisplacementToPathClosedHere = false

scaleUniformGradientBudgetClosedHere : Bool
scaleUniformGradientBudgetClosedHere = false

clayPromotion : Bool
clayPromotion = false

r290HermitianG2SquaredCauchyClosedIsTrue :
  r290HermitianG2SquaredCauchyClosed ≡ true
r290HermitianG2SquaredCauchyClosedIsTrue = refl

clayPromotionIsFalse : clayPromotion ≡ false
clayPromotionIsFalse = refl
