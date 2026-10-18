module DASHI.Moonshine.JInvariantEisensteinTruncationIncrementExact where

------------------------------------------------------------------------
-- LITERAL SUCCESSOR INCREMENTS OF THE FINITE E4/E6 TRAJECTORIES
--
-- DASHI CONTRIBUTION / CROSS-POLLINATION
--
-- The application-neutral summable-increment Cauchy lane asks consumers to
-- identify one literal trajectory and its adjacent increments before supplying
-- any magnitude/tail estimate.  The finite Eisenstein owner already defines
-- E4_N and E6_N by successor recurrence.  This module exposes those exact
-- increments, on the same ConcreteComplex carrier, so later convergence work
-- cannot accidentally reason about a parallel q-series.
--
-- No absolute-value bound, q-decay theorem, Cauchy conclusion, infinite-series
-- promotion, or analytic Eisenstein identification is introduced here.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; suc; _*_)

import DASHI.Analysis.ConstructiveRealSpine as Real
import DASHI.Analysis.ConcreteComplex as Complex
import DASHI.Moonshine.JInvariantEisensteinFiniteQSeriesExact as Finite

ROf : Complex.ConstructedComplexPackage -> Real.ConstructedOrderedCompleteReal
  ROf C = Real.real (Complex.realPackage C)

e4Increment :
  (C : Complex.ConstructedComplexPackage) ->
  Finite.DivisorPowerKernel ->
  Nat ->
  Complex.ComplexPair (ROf C) ->
  Complex.ComplexPair (ROf C)
e4Increment C kernel n tau =
  Finite.scaleNatC
    (240 * Finite.sigma3 kernel (suc n))
    (Finite.powC (Finite.qOf C tau) (suc n))

e6Increment :
  (C : Complex.ConstructedComplexPackage) ->
  Finite.DivisorPowerKernel ->
  Nat ->
  Complex.ComplexPair (ROf C) ->
  Complex.ComplexPair (ROf C)
e6Increment C kernel n tau =
  Finite.scaleNatC
    (504 * Finite.sigma5 kernel (suc n))
    (Finite.powC (Finite.qOf C tau) (suc n))

e4SuccessorIsPreviousPlusIncrement :
  (C : Complex.ConstructedComplexPackage) ->
  (kernel : Finite.DivisorPowerKernel) ->
  (tau : Complex.ComplexPair (ROf C)) ->
  (n : Nat) ->
  Finite.e4Truncated C kernel (suc n) tau
  ≡ Complex._+C_
      (Finite.e4Truncated C kernel n tau)
      (e4Increment C kernel n tau)
e4SuccessorIsPreviousPlusIncrement C kernel tau n = refl

e6SuccessorIsPreviousMinusIncrement :
  (C : Complex.ConstructedComplexPackage) ->
  (kernel : Finite.DivisorPowerKernel) ->
  (tau : Complex.ComplexPair (ROf C)) ->
  (n : Nat) ->
  Finite.e6Truncated C kernel (suc n) tau
  ≡ Complex._-C_
      (Finite.e6Truncated C kernel n tau)
      (e6Increment C kernel n tau)
e6SuccessorIsPreviousMinusIncrement C kernel tau n = refl

------------------------------------------------------------------------
-- Componentwise forms consumed by the same-carrier Cauchy compiler.
------------------------------------------------------------------------

e4RealSuccessorIncrement :
  (C : Complex.ConstructedComplexPackage) ->
  (kernel : Finite.DivisorPowerKernel) ->
  (tau : Complex.ComplexPair (ROf C)) ->
  (n : Nat) ->
  Complex.re (Finite.e4Truncated C kernel (suc n) tau)
  ≡ Real._+_ (ROf C)
      (Complex.re (Finite.e4Truncated C kernel n tau))
      (Complex.re (e4Increment C kernel n tau))
e4RealSuccessorIncrement C kernel tau n = refl

e4ImagSuccessorIncrement :
  (C : Complex.ConstructedComplexPackage) ->
  (kernel : Finite.DivisorPowerKernel) ->
  (tau : Complex.ComplexPair (ROf C)) ->
  (n : Nat) ->
  Complex.im (Finite.e4Truncated C kernel (suc n) tau)
  ≡ Real._+_ (ROf C)
      (Complex.im (Finite.e4Truncated C kernel n tau))
      (Complex.im (e4Increment C kernel n tau))
e4ImagSuccessorIncrement C kernel tau n = refl

e6RealSuccessorIncrement :
  (C : Complex.ConstructedComplexPackage) ->
  (kernel : Finite.DivisorPowerKernel) ->
  (tau : Complex.ComplexPair (ROf C)) ->
  (n : Nat) ->
  Complex.re (Finite.e6Truncated C kernel (suc n) tau)
  ≡ Real._-_ (ROf C)
      (Complex.re (Finite.e6Truncated C kernel n tau))
      (Complex.re (e6Increment C kernel n tau))
e6RealSuccessorIncrement C kernel tau n = refl

e6ImagSuccessorIncrement :
  (C : Complex.ConstructedComplexPackage) ->
  (kernel : Finite.DivisorPowerKernel) ->
  (tau : Complex.ComplexPair (ROf C)) ->
  (n : Nat) ->
  Complex.im (Finite.e6Truncated C kernel (suc n) tau)
  ≡ Real._-_ (ROf C)
      (Complex.im (Finite.e6Truncated C kernel n tau))
      (Complex.im (e6Increment C kernel n tau))
e6ImagSuccessorIncrement C kernel tau n = refl
