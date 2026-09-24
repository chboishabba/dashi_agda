module DASHI.Moonshine.JInvariantQPowerModulusExact where

------------------------------------------------------------------------
-- MODULUS PROPAGATION FOR THE LITERAL q POWERS
--
-- DASHI CONTRIBUTION / CROSS-POLLINATION
--
-- The finite Eisenstein recurrence uses the existing executable powC on q.
-- Once the selected ordinary complex package supplies the standard
-- multiplicative modulus laws on that SAME carrier, no further analytic
-- theorem is needed to identify the modulus of the power:
--
--   |q^n| = |q|^n.
--
-- This owner deliberately does not manufacture modulus multiplicativity from
-- the very small legacy ConstructedOrderedCompleteReal spine.  The quantum
-- and physics-linear-analysis lanes independently expose norm/modulus law
-- shapes, but neither is silently promoted into this transcendental package.
------------------------------------------------------------------------

open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; cong₂)
open import Agda.Builtin.Nat using (Nat; zero; suc)

import DASHI.Analysis.ConstructiveRealSpine as Real
import DASHI.Analysis.ConstructiveSeries as Series
import DASHI.Analysis.ConcreteComplex as Complex
import DASHI.Analysis.OrdinaryComplexPolar as Polar
import DASHI.Moonshine.JInvariantEisensteinFiniteQSeriesExact as Finite

record ComplexModulusMultiplicationLaws
    (C : Complex.ConstructedComplexPackage)
    (D : Polar.RealDivisionAndSquareRoot
      (Real.real (Complex.realPackage C)))
    (F : Polar.ComplexFieldAuthority
      (Real.real (Complex.realPackage C)) D) : Set₁ where
  private
    R = Real.real (Complex.realPackage C)
  field
    modulusOne :
      Polar.modulus F (Complex.oneC {R}) ≡ Real.one R

    modulusMultiply :
      ∀ left right →
      Polar.modulus F (Complex._*C_ left right)
      ≡ Real._*_ R
          (Polar.modulus F left)
          (Polar.modulus F right)

open ComplexModulusMultiplicationLaws public

qPowerModulus :
  ∀ {C : Complex.ConstructedComplexPackage}
    {D : Polar.RealDivisionAndSquareRoot
      (Real.real (Complex.realPackage C))}
    {F : Polar.ComplexFieldAuthority
      (Real.real (Complex.realPackage C)) D} →
  (M : ComplexModulusMultiplicationLaws C D F) →
  (tau : Complex.ComplexPair (Real.real (Complex.realPackage C))) →
  (n : Nat) →
  Polar.modulus F (Finite.powC (Finite.qOf C tau) n)
  ≡ Series.powerR
      (Real.real (Complex.realPackage C))
      (Polar.modulus F (Finite.qOf C tau))
      n
qPowerModulus {C} {D} {F} M tau zero =
  modulusOne M
qPowerModulus {C} {D} {F} M tau (suc n) =
  trans
    (modulusMultiply M
      (Finite.qOf C tau)
      (Finite.powC (Finite.qOf C tau) n))
    (cong₂
      (Real._*_ (Real.real (Complex.realPackage C)))
      refl
      (qPowerModulus M tau n))
