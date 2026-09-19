module DASHI.Moonshine.JInvariantQPowerModulusValidation where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Analysis.ConstructiveRealSpine as Real
import DASHI.Analysis.ConstructiveSeries as Series
import DASHI.Analysis.ConcreteComplex as Complex
import DASHI.Analysis.OrdinaryComplexPolar as Polar
import DASHI.Moonshine.JInvariantEisensteinFiniteQSeriesExact as Finite
import DASHI.Moonshine.JInvariantQPowerModulusExact as P

qPowerModulusRegression :
  ∀ {C : Complex.ConstructedComplexPackage}
    {D : Polar.RealDivisionAndSquareRoot
      (Real.real (Complex.realPackage C))}
    {F : Polar.ComplexFieldAuthority
      (Real.real (Complex.realPackage C)) D} →
  (M : P.ComplexModulusMultiplicationLaws C D F) →
  (tau : Complex.ComplexPair (Real.real (Complex.realPackage C))) →
  (n : Nat) →
  Polar.modulus F (Finite.powC (Finite.qOf C tau) n)
  ≡ Series.powerR
      (Real.real (Complex.realPackage C))
      (Polar.modulus F (Finite.qOf C tau))
      n
qPowerModulusRegression = P.qPowerModulus
