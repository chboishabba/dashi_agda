module DASHI.Moonshine.JInvariantEisensteinFiniteQSeriesExact where

------------------------------------------------------------------------
-- EXECUTABLE FINITE E4/E6 q-SERIES ON THE CONSTRUCTED COMPLEX CARRIER
--
-- Runtime parity target:
--   scripts/cm_j_alpha_scan.py
--
-- Formulae used there and here:
--   q(tau) = exp(2*pi*i*tau)
--   E4_N = 1 + 240 * sum_{n=1..N} sigma_3(n) q^n
--   E6_N = 1 - 504 * sum_{n=1..N} sigma_5(n) q^n
--
-- sigma_3 and sigma_5 are explicit inputs here.  The existing Python producer
-- computes them by divisor enumeration.  This module owns the q-series
-- recurrence and complex evaluation but does not silently promote the finite
-- truncation to the converged modular forms.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat; zero; suc; _*_)

import DASHI.Analysis.ConstructiveRealSpine as Real
import DASHI.Analysis.ConcreteComplex as Complex

------------------------------------------------------------------------
-- Primitive exact finite arithmetic.
------------------------------------------------------------------------

scaleNatC :
  ∀ {R : Real.ConstructedOrderedCompleteReal} →
  Nat → Complex.ComplexPair R → Complex.ComplexPair R
scaleNatC zero z = Complex.zeroC
scaleNatC (suc n) z = Complex._+C_ z (scaleNatC n z)

powC :
  ∀ {R : Real.ConstructedOrderedCompleteReal} →
  Complex.ComplexPair R → Nat → Complex.ComplexPair R
powC z zero = Complex.oneC
powC z (suc n) = Complex._*C_ z (powC z n)

squareC :
  ∀ {R : Real.ConstructedOrderedCompleteReal} →
  Complex.ComplexPair R → Complex.ComplexPair R
squareC z = Complex._*C_ z z

cubeC :
  ∀ {R : Real.ConstructedOrderedCompleteReal} →
  Complex.ComplexPair R → Complex.ComplexPair R
cubeC z = Complex._*C_ (squareC z) z

------------------------------------------------------------------------
-- Divisor-power producer boundary.  Runtime currently comes from the existing
-- sigma_power function in scripts/cm_j_alpha_scan.py.
------------------------------------------------------------------------

record DivisorPowerKernel : Set where
  constructor divisor-power-kernel
  field
    sigma3 : Nat → Nat
    sigma5 : Nat → Nat

open DivisorPowerKernel public

------------------------------------------------------------------------
-- q = exp(2*pi*i*tau) on the same constructed complex package.
------------------------------------------------------------------------

qOf :
  (C : Complex.ConstructedComplexPackage) →
  Complex.ComplexPair (Real.real (Complex.realPackage C)) →
  Complex.ComplexPair (Real.real (Complex.realPackage C))
qOf C tau =
  let
    R = Real.real (Complex.realPackage C)
    CE = Complex.complexExponential C
    piC = Complex.complex (Complex.pi CE) (Real.zero R)
    twoPiI = scaleNatC 2 (Complex._*C_ Complex.imaginaryUnit piC)
  in
  Complex.expC CE (Complex._*C_ twoPiI tau)

------------------------------------------------------------------------
-- Exact finite recurrences.  At step suc n we append the n+1 term, avoiding a
-- second finite-sum architecture.
------------------------------------------------------------------------

e4Truncated :
  (C : Complex.ConstructedComplexPackage) →
  DivisorPowerKernel →
  Nat →
  Complex.ComplexPair (Real.real (Complex.realPackage C)) →
  Complex.ComplexPair (Real.real (Complex.realPackage C))
e4Truncated C kernel zero tau = Complex.oneC
e4Truncated C kernel (suc n) tau =
  Complex._+C_
    (e4Truncated C kernel n tau)
    (scaleNatC
      (240 * sigma3 kernel (suc n))
      (powC (qOf C tau) (suc n)))

e6Truncated :
  (C : Complex.ConstructedComplexPackage) →
  DivisorPowerKernel →
  Nat →
  Complex.ComplexPair (Real.real (Complex.realPackage C)) →
  Complex.ComplexPair (Real.real (Complex.realPackage C))
e6Truncated C kernel zero tau = Complex.oneC
e6Truncated C kernel (suc n) tau =
  Complex._-C_
    (e6Truncated C kernel n tau)
    (scaleNatC
      (504 * sigma5 kernel (suc n))
      (powC (qOf C tau) (suc n)))

discriminantNumeratorTruncated :
  (C : Complex.ConstructedComplexPackage) →
  DivisorPowerKernel →
  Nat →
  Complex.ComplexPair (Real.real (Complex.realPackage C)) →
  Complex.ComplexPair (Real.real (Complex.realPackage C))
discriminantNumeratorTruncated C kernel terms tau =
  Complex._-C_
    (cubeC (e4Truncated C kernel terms tau))
    (squareC (e6Truncated C kernel terms tau))

------------------------------------------------------------------------
-- Runtime/source boundary.
------------------------------------------------------------------------

record EisensteinFiniteQSeriesFrontier : Set where
  constructor eisenstein-finite-q-series-frontier
  field
    qUsesConstructedComplexExponential : Bool
    e4FiniteRecurrenceExecutable : Bool
    e6FiniteRecurrenceExecutable : Bool
    discriminantNumeratorExecutable : Bool
    divisorPowerKernelStillExternal : Bool
    finiteTruncationEqualsInfiniteSeriesProved : Bool
    finiteTruncationIsAnalyticJAutomatically : Bool

canonicalEisensteinFiniteQSeriesFrontier : EisensteinFiniteQSeriesFrontier
canonicalEisensteinFiniteQSeriesFrontier =
  eisenstein-finite-q-series-frontier
    true true true true true false false
