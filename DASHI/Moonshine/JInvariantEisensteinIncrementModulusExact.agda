module DASHI.Moonshine.JInvariantEisensteinIncrementModulusExact where

------------------------------------------------------------------------
-- SAME-CARRIER MODULUS BOUNDS FOR THE LITERAL E4/E6 INCREMENTS
--
-- DASHI CONTRIBUTION / CROSS-POLLINATION
--
-- The coefficient action in the finite Eisenstein recurrence is not an
-- abstract scalar multiplication: scaleNatC implements multiplication by a
-- natural as repeated complex addition.  Therefore a triangle inequality,
-- together with the ordinary order laws needed to transport inequalities
-- through addition, is enough to prove
--
--   |scaleNatC k z| <= k * |z|
--
-- in the repository's recursive natural-scaling normal form.
--
-- Combining that with JInvariantQPowerModulusExact gives exact same-carrier
-- bounds for the actual appended E4/E6 terms.  Polynomial coefficient
-- envelopes and |q|<1 are separate already-owned inputs; summability and
-- IsCauchy remain downstream.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl; subst; sym)
open import Agda.Builtin.Nat using (Nat; zero; suc; _*_)
open import Data.Nat.Base using (_≤_; z≤n; s≤s)

import DASHI.Analysis.ConstructiveRealSpine as Real
import DASHI.Analysis.ConstructiveSeries as Series
import DASHI.Analysis.ConcreteComplex as Complex
import DASHI.Analysis.OrdinaryComplexPolar as Polar
import DASHI.Mathematics.NumberTheory.FiniteDivisorPowerSumExact as Divisor
import DASHI.Moonshine.JInvariantEisensteinFiniteQSeriesExact as Finite
import DASHI.Moonshine.JInvariantEisensteinTruncationIncrementExact as Increment
import DASHI.Moonshine.JInvariantEisensteinIncrementCoefficientBoundExact as Coefficient
import DASHI.Moonshine.JInvariantEisensteinInternalDivisorPowerKernelExact as Internal
import DASHI.Moonshine.JInvariantQPowerModulusExact as QPower

scaleNatR :
  (R : Real.ConstructedOrderedCompleteReal) ->
  Nat -> Real.Real R -> Real.Real R
scaleNatR R zero x = Real.zero R
scaleNatR R (suc n) x = Real._+_ R x (scaleNatR R n x)

record ComplexModulusTriangleOrderLaws
    (C : Complex.ConstructedComplexPackage)
    (D : Polar.RealDivisionAndSquareRoot
      (Real.real (Complex.realPackage C)))
    (F : Polar.ComplexFieldAuthority
      (Real.real (Complex.realPackage C)) D) : Set₁ where
  private
    R = Real.real (Complex.realPackage C)
  field
    modulusZero :
      Polar.modulus F (Complex.zeroC {R}) ≡ Real.zero R

    modulusTriangle :
      ∀ left right ->
      Real._≤_ R
        (Polar.modulus F (Complex._+C_ left right))
        (Real._+_ R
          (Polar.modulus F left)
          (Polar.modulus F right))

    leRefl : ∀ x -> Real._≤_ R x x

    leTrans :
      ∀ {x y z} ->
      Real._≤_ R x y ->
      Real._≤_ R y z ->
      Real._≤_ R x z

    addLeftMonotone :
      ∀ fixed {left right} ->
      Real._≤_ R left right ->
      Real._≤_ R
        (Real._+_ R fixed left)
        (Real._+_ R fixed right)

    addNonnegative :
      ∀ {left right} ->
      Real._≤_ R (Real.zero R) left ->
      Real._≤_ R (Real.zero R) right ->
      Real._≤_ R (Real.zero R) (Real._+_ R left right)

open ComplexModulusTriangleOrderLaws public

scaleNatCModulusBound :
  ∀ {C : Complex.ConstructedComplexPackage}
    {D : Polar.RealDivisionAndSquareRoot
      (Real.real (Complex.realPackage C))}
    {F : Polar.ComplexFieldAuthority
      (Real.real (Complex.realPackage C)) D} ->
  (T : ComplexModulusTriangleOrderLaws C D F) ->
  (n : Nat) ->
  (z : Complex.ComplexPair (Real.real (Complex.realPackage C))) ->
  Real._≤_ (Real.real (Complex.realPackage C))
    (Polar.modulus F (Finite.scaleNatC n z))
    (scaleNatR
      (Real.real (Complex.realPackage C))
      n
      (Polar.modulus F z))
scaleNatCModulusBound {C} {D} {F} T zero z =
  subst
    (λ value ->
      Real._≤_ (Real.real (Complex.realPackage C))
        value
        (Real.zero (Real.real (Complex.realPackage C))))
    (sym (modulusZero T))
    (leRefl T (Real.zero (Real.real (Complex.realPackage C))))
scaleNatCModulusBound {C} {D} {F} T (suc n) z =
  leTrans T
    (modulusTriangle T z (Finite.scaleNatC n z))
    (addLeftMonotone T
      (Polar.modulus F z)
      (scaleNatCModulusBound T n z))

e4IncrementModulusBound :
  ∀ {C : Complex.ConstructedComplexPackage}
    {D : Polar.RealDivisionAndSquareRoot
      (Real.real (Complex.realPackage C))}
    {F : Polar.ComplexFieldAuthority
      (Real.real (Complex.realPackage C)) D} ->
  (M : QPower.ComplexModulusMultiplicationLaws C D F) ->
  (T : ComplexModulusTriangleOrderLaws C D F) ->
  (kernel : Finite.DivisorPowerKernel) ->
  (tau : Complex.ComplexPair (Real.real (Complex.realPackage C))) ->
  (n : Nat) ->
  Real._≤_ (Real.real (Complex.realPackage C))
    (Polar.modulus F (Increment.e4Increment C kernel n tau))
    (scaleNatR
      (Real.real (Complex.realPackage C))
      (240 * Finite.sigma3 kernel (suc n))
      (Series.powerR
        (Real.real (Complex.realPackage C))
        (Polar.modulus F (Finite.qOf C tau))
        (suc n)))
e4IncrementModulusBound {C} {D} {F} M T kernel tau n =
  subst
    (λ magnitude ->
      Real._≤_ (Real.real (Complex.realPackage C))
        (Polar.modulus F (Increment.e4Increment C kernel n tau))
        (scaleNatR
          (Real.real (Complex.realPackage C))
          (240 * Finite.sigma3 kernel (suc n))
          magnitude))
    (QPower.qPowerModulus M tau (suc n))
    (scaleNatCModulusBound T
      (240 * Finite.sigma3 kernel (suc n))
      (Finite.powC (Finite.qOf C tau) (suc n)))

e6IncrementModulusBound :
  ∀ {C : Complex.ConstructedComplexPackage}
    {D : Polar.RealDivisionAndSquareRoot
      (Real.real (Complex.realPackage C))}
    {F : Polar.ComplexFieldAuthority
      (Real.real (Complex.realPackage C)) D} ->
  (M : QPower.ComplexModulusMultiplicationLaws C D F) ->
  (T : ComplexModulusTriangleOrderLaws C D F) ->
  (kernel : Finite.DivisorPowerKernel) ->
  (tau : Complex.ComplexPair (Real.real (Complex.realPackage C))) ->
  (n : Nat) ->
  Real._≤_ (Real.real (Complex.realPackage C))
    (Polar.modulus F (Increment.e6Increment C kernel n tau))
    (scaleNatR
      (Real.real (Complex.realPackage C))
      (504 * Finite.sigma5 kernel (suc n))
      (Series.powerR
        (Real.real (Complex.realPackage C))
        (Polar.modulus F (Finite.qOf C tau))
        (suc n)))
e6IncrementModulusBound {C} {D} {F} M T kernel tau n =
  subst
    (λ magnitude ->
      Real._≤_ (Real.real (Complex.realPackage C))
        (Polar.modulus F (Increment.e6Increment C kernel n tau))
        (scaleNatR
          (Real.real (Complex.realPackage C))
          (504 * Finite.sigma5 kernel (suc n))
          magnitude))
    (QPower.qPowerModulus M tau (suc n))
    (scaleNatCModulusBound T
      (504 * Finite.sigma5 kernel (suc n))
      (Finite.powC (Finite.qOf C tau) (suc n)))


------------------------------------------------------------------------
-- Natural coefficient transport.
------------------------------------------------------------------------

scaleNatRNonnegative :
  ∀ {C : Complex.ConstructedComplexPackage}
    {D : Polar.RealDivisionAndSquareRoot
      (Real.real (Complex.realPackage C))}
    {F : Polar.ComplexFieldAuthority
      (Real.real (Complex.realPackage C)) D} ->
  (T : ComplexModulusTriangleOrderLaws C D F) ->
  (n : Nat) ->
  (x : Real.Real (Real.real (Complex.realPackage C))) ->
  Real._≤_ (Real.real (Complex.realPackage C))
    (Real.zero (Real.real (Complex.realPackage C))) x ->
  Real._≤_ (Real.real (Complex.realPackage C))
    (Real.zero (Real.real (Complex.realPackage C)))
    (scaleNatR (Real.real (Complex.realPackage C)) n x)
scaleNatRNonnegative {C} T zero x xNN =
  leRefl T (Real.zero (Real.real (Complex.realPackage C)))
scaleNatRNonnegative {C} T (suc n) x xNN =
  addNonnegative T xNN (scaleNatRNonnegative T n x xNN)

scaleNatRMonotoneCount :
  ∀ {C : Complex.ConstructedComplexPackage}
    {D : Polar.RealDivisionAndSquareRoot
      (Real.real (Complex.realPackage C))}
    {F : Polar.ComplexFieldAuthority
      (Real.real (Complex.realPackage C)) D}
    {left right : Nat} ->
  (T : ComplexModulusTriangleOrderLaws C D F) ->
  left ≤ right ->
  (x : Real.Real (Real.real (Complex.realPackage C))) ->
  Real._≤_ (Real.real (Complex.realPackage C))
    (Real.zero (Real.real (Complex.realPackage C))) x ->
  Real._≤_ (Real.real (Complex.realPackage C))
    (scaleNatR (Real.real (Complex.realPackage C)) left x)
    (scaleNatR (Real.real (Complex.realPackage C)) right x)
scaleNatRMonotoneCount {C} T {zero} {right} z≤n x xNN =
  scaleNatRNonnegative T right x xNN
scaleNatRMonotoneCount {C} T {suc left} {suc right} (s≤s left≤right) x xNN =
  addLeftMonotone T x
    (scaleNatRMonotoneCount T left≤right x xNN)

qPowerModulusNonnegative :
  ∀ {C : Complex.ConstructedComplexPackage}
    {D : Polar.RealDivisionAndSquareRoot
      (Real.real (Complex.realPackage C))}
    {F : Polar.ComplexFieldAuthority
      (Real.real (Complex.realPackage C)) D} ->
  (M : QPower.ComplexModulusMultiplicationLaws C D F) ->
  (tau : Complex.ComplexPair (Real.real (Complex.realPackage C))) ->
  (n : Nat) ->
  Real._≤_ (Real.real (Complex.realPackage C))
    (Real.zero (Real.real (Complex.realPackage C)))
    (Series.powerR
      (Real.real (Complex.realPackage C))
      (Polar.modulus F (Finite.qOf C tau))
      n)
qPowerModulusNonnegative {C} {D} {F} M tau n =
  subst
    (λ value ->
      Real._≤_ (Real.real (Complex.realPackage C))
        (Real.zero (Real.real (Complex.realPackage C)))
        value)
    (QPower.qPowerModulus M tau n)
    (Polar.sqrtNonnegativeResult D
      (Complex.normSqC (Finite.powC (Finite.qOf C tau) n))
      (Polar.normSqNonnegative F
        (Finite.powC (Finite.qOf C tau) n)))

e4InternalPolynomialGeometricModulusBound :
  ∀ {C : Complex.ConstructedComplexPackage}
    {D : Polar.RealDivisionAndSquareRoot
      (Real.real (Complex.realPackage C))}
    {F : Polar.ComplexFieldAuthority
      (Real.real (Complex.realPackage C)) D} ->
  (M : QPower.ComplexModulusMultiplicationLaws C D F) ->
  (T : ComplexModulusTriangleOrderLaws C D F) ->
  (tau : Complex.ComplexPair (Real.real (Complex.realPackage C))) ->
  (n : Nat) ->
  Real._≤_ (Real.real (Complex.realPackage C))
    (Polar.modulus F
      (Increment.e4Increment C Internal.internalDivisorPowerKernel n tau))
    (scaleNatR
      (Real.real (Complex.realPackage C))
      (240 * (Divisor.powNat (suc n) 3 * suc n))
      (Series.powerR
        (Real.real (Complex.realPackage C))
        (Polar.modulus F (Finite.qOf C tau))
        (suc n)))
e4InternalPolynomialGeometricModulusBound {C} M T tau n =
  leTrans T
    (e4IncrementModulusBound M T Internal.internalDivisorPowerKernel tau n)
    (scaleNatRMonotoneCount T
      (Coefficient.e4IncrementCoefficientBound n)
      (Series.powerR
        (Real.real (Complex.realPackage C))
        (Polar.modulus _ (Finite.qOf C tau))
        (suc n))
      (qPowerModulusNonnegative M tau (suc n)))

e6InternalPolynomialGeometricModulusBound :
  ∀ {C : Complex.ConstructedComplexPackage}
    {D : Polar.RealDivisionAndSquareRoot
      (Real.real (Complex.realPackage C))}
    {F : Polar.ComplexFieldAuthority
      (Real.real (Complex.realPackage C)) D} ->
  (M : QPower.ComplexModulusMultiplicationLaws C D F) ->
  (T : ComplexModulusTriangleOrderLaws C D F) ->
  (tau : Complex.ComplexPair (Real.real (Complex.realPackage C))) ->
  (n : Nat) ->
  Real._≤_ (Real.real (Complex.realPackage C))
    (Polar.modulus F
      (Increment.e6Increment C Internal.internalDivisorPowerKernel n tau))
    (scaleNatR
      (Real.real (Complex.realPackage C))
      (504 * (Divisor.powNat (suc n) 5 * suc n))
      (Series.powerR
        (Real.real (Complex.realPackage C))
        (Polar.modulus F (Finite.qOf C tau))
        (suc n)))
e6InternalPolynomialGeometricModulusBound {C} M T tau n =
  leTrans T
    (e6IncrementModulusBound M T Internal.internalDivisorPowerKernel tau n)
    (scaleNatRMonotoneCount T
      (Coefficient.e6IncrementCoefficientBound n)
      (Series.powerR
        (Real.real (Complex.realPackage C))
        (Polar.modulus _ (Finite.qOf C tau))
        (suc n))
      (qPowerModulusNonnegative M tau (suc n)))
