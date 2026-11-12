module DASHI.Moonshine.AbelBishopInverseKoenigsRemainderToSchroederExact where

------------------------------------------------------------------------
-- SAME-SOURCE LOCAL LOG QUADRATIC REMAINDER -> SCHROEDER.
--
-- This is the exact max-cut compiler:
--
--  source bound on |component(p^n * p * R_p(g^n(z)))|
--       => bound on actual h_(n+1)(z)-h_n(z)
--       => original Bishop geometric-series limit for h_n
--       => p * Psi(g(z)) ~= Psi(z).
--
-- The analytical leaf is a bound on the LITERAL Bishop logarithm
-- remainder and original p-power. The leaf is NOT postulated,
-- auto-inhabited or substituted with numerical estimates.
--
-- The SAME endomap, p, point z, and z'=g(z) occur throughout.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Data.Product.Base using (_,_; proj₁; proj₂)

import Real as BishopReal
import RealProperties as BishopP

import DASHI.Analysis.BishopComplexSeriesConvergenceExact as Complex
import DASHI.Analysis.BishopComplexAlgebraExact as Algebra
import DASHI.Analysis.BishopComplexReciprocalExact as Reciprocal
import DASHI.Foundations.BishopPolynomialGeometricDominationConvergenceExact as Geometric
import DASHI.Moonshine.AbelBishopKoenigsFiniteTelescopingExact as Telescope
import DASHI.Moonshine.AbelBishopKoenigsGeometricAbsoluteExact as Bounds
import DASHI.Moonshine.AbelBishopInverseKoenigsFiniteOrbitExact as Orbit
import DASHI.Moonshine.AbelBishopInverseKoenigsRemainderFactorExact as Remainder
import DASHI.Moonshine.AbelBishopInverseKoenigsGeometricOrbitExact as Limit
import DASHI.Moonshine.AbelBishopInverseKoenigsGeometricSchroederExact as Schroeder

originalBishopScaledLogRemainder :
  (p : Complex.BishopComplex) →
  (nz : Reciprocal.BishopComplexNonzero p) →
  (g : Complex.BishopComplex → Complex.BishopComplex) →
  Nat → Complex.BishopComplex → Complex.BishopComplex
originalBishopScaledLogRemainder p nz g n z =
  Algebra._*C_ (Algebra.powC p n)
    (Algebra._*C_ p
      (Remainder.originalBishopLogLocalTaylorRemainder
        p nz g (Orbit.inverseOrbit g n z)))

record OriginalBishopSelectedLogRemainderBounds
    (p : Complex.BishopComplex)
    (nz : Reciprocal.BishopComplexNonzero p)
    (g : Complex.BishopComplex → Complex.BishopComplex)
    (z : Complex.BishopComplex)
    (constant ratio : BishopReal.ℝ) : Set₁ where
  field
    -- Actual Bishop nonnegative constant and [0,1) geometric ratio,
    -- not copied real or floating point scalars.
    geometricInputs :
      Geometric.BishopScaledGeometricInputs constant ratio

    realRemainderBound :
      ∀ n →
      BishopReal._≤_
        (BishopReal.∣ Complex.re
          (originalBishopScaledLogRemainder p nz g n z) ∣)
        (Geometric.scaledGeometricTerm constant ratio n)

    imagRemainderBound :
      ∀ n →
      BishopReal._≤_
        (BishopReal.∣ Complex.im
          (originalBishopScaledLogRemainder p nz g n z) ∣)
        (Geometric.scaledGeometricTerm constant ratio n)

open OriginalBishopSelectedLogRemainderBounds public

originalBishopRemainderBuildsActualIncrementBounds :
  ∀ p (nz : Reciprocal.BishopComplexNonzero p) g z constant ratio →
  OriginalBishopSelectedLogRemainderBounds
    p nz g z constant ratio →
  Bounds.OriginalBishopGeometricComponentBounds
    (Telescope.originalBishopComplexStepDifference
      (λ n → Orbit.inverseKoenigsPrefix p g n z))
    constant ratio
originalBishopRemainderBuildsActualIncrementBounds
  p nz g z constant ratio bounds =
  record
    { Bounds.geometricInputs = geometricInputs bounds
    ; Bounds.realComponentBound = λ n →
        BishopP.≤-respˡ-≃
          (BishopP.∣-∣-cong
            (proj₁
              (Remainder.originalBishopInverseKoenigsDifferenceIsScaledRemainder
                p nz g n z)))
          (realRemainderBound bounds n)
    ; Bounds.imaginaryComponentBound = λ n →
        BishopP.≤-respˡ-≃
          (BishopP.∣-∣-cong
            (proj₂
              (Remainder.originalBishopInverseKoenigsDifferenceIsScaledRemainder
                p nz g n z)))
          (imagRemainderBound bounds n)
    }

originalBishopRemainderSourceKoenigsLimit :
  ∀ p (nz : Reciprocal.BishopComplexNonzero p)
    g z constant ratio →
  (bounds : OriginalBishopSelectedLogRemainderBounds
    p nz g z constant ratio) →
  Complex.BishopComplex
originalBishopRemainderSourceKoenigsLimit
  p nz g z constant ratio bounds =
  Limit.originalBishopInverseKoenigsGeometricLimit
    p g z constant ratio
    (originalBishopRemainderBuildsActualIncrementBounds
      p nz g z constant ratio bounds)

originalBishopRemainderBuildsSchroeder :
  ∀ p (nz : Reciprocal.BishopComplexNonzero p)
    g z constant ratio →
  (atZ : OriginalBishopSelectedLogRemainderBounds
    p nz g z constant ratio) →
  (atGZ : OriginalBishopSelectedLogRemainderBounds
    p nz g (g z) constant ratio) →
  Complex._≈C_
    (Algebra._*C_ p
      (originalBishopRemainderSourceKoenigsLimit
        p nz g (g z) constant ratio atGZ))
    (originalBishopRemainderSourceKoenigsLimit
      p nz g z constant ratio atZ)
originalBishopRemainderBuildsSchroeder
  p nz g z constant ratio atZ atGZ =
  Schroeder.originalBishopInverseKoenigsGeometricSchroeder
    p g z constant ratio
    (originalBishopRemainderBuildsActualIncrementBounds
      p nz g z constant ratio atZ)
    (originalBishopRemainderBuildsActualIncrementBounds
      p nz g (g z) constant ratio atGZ)
