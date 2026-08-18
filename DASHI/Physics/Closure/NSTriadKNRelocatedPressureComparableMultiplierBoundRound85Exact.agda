module DASHI.Physics.Closure.NSTriadKNRelocatedPressureComparableMultiplierBoundRound85Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- Author: Marco Cannone.
-- Title: "Harmonic Analysis Tools for Solving the Incompressible
-- Navier-Stokes Equations".
-- DOI: 10.1016/S1874-5792(05)80006-0.
--
-- ROUND85 / COMPARABLE PRESSURE LEG IS AN ORDER-ZERO MULTIPLIER
--
-- The relocated pressure scalar differs from the Poisson source by
--
--   -(p dot k)/|p|^2.
--
-- On a nonzero rational mode p with inverse-square coefficient i_p, assume
--
--   i_p |p|^2 = 1,
--   |k|^2 <= C^2 |p|^2.
--
-- Exact finite Cauchy--Schwarz gives
--
--   (p dot k)^2 <= |p|^2 |k|^2,
--
-- and therefore
--
--   [i_p (p dot k)]^2 <= C^2.
--
-- Multiplying by the square of the pressure-source coefficient proves that
-- the relocated scalar costs at most C^2 in squared norm.  No division or
-- square root is required.  Consequently the Round85 relocated term is
-- analytically difficult only when the pressure leg is genuinely low relative
-- to the output; comparable/high legs are order zero.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; _*_; _≤_; nonNegative)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; subst; trans)

import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as L2
import DASHI.Physics.Closure.NSTriadKNLuoRationalLerayMultiplierContractiveExact as Leray

record ComparablePressureRatioDatum : Set where
  field
    pressureMode outputMode : Leray.Vec3
    inversePressureNormSquared comparisonSquared sourceCoefficient : ℚ

    inverseNonnegative : 0ℚ ≤ inversePressureNormSquared
    comparisonSquaredNonnegative : 0ℚ ≤ comparisonSquared
    inverseCalibration :
      inversePressureNormSquared * Leray.vecNormSquared pressureMode ≡ 1ℚ
    outputComparable :
      Leray.vecNormSquared outputMode
      ≤ comparisonSquared * Leray.vecNormSquared pressureMode

open ComparablePressureRatioDatum public

relocationRatio : ComparablePressureRatioDatum → ℚ
relocationRatio datum =
  inversePressureNormSquared datum
  * Leray.vecDot (pressureMode datum) (outputMode datum)

relocatedCoefficient : ComparablePressureRatioDatum → ℚ
relocatedCoefficient datum =
  relocationRatio datum * sourceCoefficient datum

ratioSquareFactors : ∀ datum →
  L2.square (relocationRatio datum)
  ≡ L2.square (inversePressureNormSquared datum)
      * L2.square (Leray.vecDot (pressureMode datum) (outputMode datum))
ratioSquareFactors datum =
  solve
    ( inversePressureNormSquared datum
    ∷ Leray.vecDot (pressureMode datum) (outputMode datum)
    ∷ [])

inverseSquareNonnegative : ∀ datum →
  0ℚ ≤ L2.square (inversePressureNormSquared datum)
inverseSquareNonnegative datum =
  L2.squareNonnegative (inversePressureNormSquared datum)

ratioSquaredBound : ∀ datum →
  L2.square (relocationRatio datum) ≤ comparisonSquared datum
ratioSquaredBound datum =
  let
    pNorm = Leray.vecNormSquared (pressureMode datum)
    kNorm = Leray.vecNormSquared (outputMode datum)
    inv = inversePressureNormSquared datum
    c2 = comparisonSquared datum
    dot = Leray.vecDot (pressureMode datum) (outputMode datum)

    cauchy : L2.square dot ≤ pNorm * kNorm
    cauchy = Leray.vectorCauchySquared (pressureMode datum) (outputMode datum)

    inv2 = L2.square inv

    instance
      inv2NN = nonNegative (inverseSquareNonnegative datum)
      invNN = nonNegative (inverseNonnegative datum)
      c2NN = nonNegative (comparisonSquaredNonnegative datum)

    cauchyScaled :
      inv2 * L2.square dot ≤ inv2 * (pNorm * kNorm)
    cauchyScaled = ℚP.*-monoˡ-≤-nonNeg inv2 cauchy

    inv2ProductMeaning :
      inv2 * (pNorm * kNorm) ≡ inv * kNorm
    inv2ProductMeaning =
      trans
        (solve (inv ∷ pNorm ∷ kNorm ∷ []))
        (cong (λ unit → inv * (unit * kNorm)) (inverseCalibration datum))

    afterCauchy :
      L2.square (relocationRatio datum) ≤ inv * kNorm
    afterCauchy =
      subst
        (λ upper → L2.square (relocationRatio datum) ≤ upper)
        inv2ProductMeaning
        (subst
          (λ lower → lower ≤ inv2 * (pNorm * kNorm))
          (ratioSquareFactors datum)
          cauchyScaled)

    comparableScaled : inv * kNorm ≤ inv * (c2 * pNorm)
    comparableScaled = ℚP.*-monoˡ-≤-nonNeg inv (outputComparable datum)

    comparableMeaning : inv * (c2 * pNorm) ≡ c2
    comparableMeaning =
      trans
        (solve (inv ∷ c2 ∷ pNorm ∷ []))
        (cong (c2 *_) (inverseCalibration datum))

    afterComparable : inv * kNorm ≤ c2
    afterComparable =
      subst (λ upper → inv * kNorm ≤ upper)
        comparableMeaning comparableScaled
  in
  ℚP.≤-trans afterCauchy afterComparable

relocatedSquareFactors : ∀ datum →
  L2.square (relocatedCoefficient datum)
  ≡ L2.square (relocationRatio datum) * L2.square (sourceCoefficient datum)
relocatedSquareFactors datum =
  solve (relocationRatio datum ∷ sourceCoefficient datum ∷ [])

relocatedCoefficientSquaredBound : ∀ datum →
  L2.square (relocatedCoefficient datum)
  ≤ comparisonSquared datum * L2.square (sourceCoefficient datum)
relocatedCoefficientSquaredBound datum =
  let
    sourceSq = L2.square (sourceCoefficient datum)
    instance sourceSqNN = nonNegative (L2.squareNonnegative (sourceCoefficient datum))
    multiplied = ℚP.*-monoʳ-≤-nonNeg sourceSq (ratioSquaredBound datum)
  in
  subst
    (λ lower → lower ≤ comparisonSquared datum * sourceSq)
    (relocatedSquareFactors datum)
    multiplied

round85ComparablePressureRelocationMultiplierBoundConstructed : Bool
round85ComparablePressureRelocationMultiplierBoundConstructed = true

round85ComparablePressureLegIsOrderZero : Bool
round85ComparablePressureLegIsOrderZero = true

round85LowPressureLegStillNeedsFirstAdjointTail : Bool
round85LowPressureLegStillNeedsFirstAdjointTail = true

round85ComparablePressureLegIsOrderZeroIsTrue :
  round85ComparablePressureLegIsOrderZero ≡ true
round85ComparablePressureLegIsOrderZeroIsTrue = refl
