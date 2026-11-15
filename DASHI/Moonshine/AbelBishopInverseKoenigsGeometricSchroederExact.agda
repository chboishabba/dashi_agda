module DASHI.Moonshine.AbelBishopInverseKoenigsGeometricSchroederExact where

------------------------------------------------------------------------
-- SELECTED INVERSE-KOENIGS SCHROEDER: ORIGINAL GEOMETRIC PRODUCER.
--
-- For the SAME selected Bishop-complex map g, multiplier p,
-- selected z and g(z), two actual source-increment geometric
-- bound certificates build the concrete limits Ψ(z), Ψ(g(z)).
--
-- Output (no caller-given convergence or unrelated limits):
--
--             p *C Ψ(g(z)) ≈C Ψ(z).
--
-- Unpaid analytic inputs are narrow and explicit:
--   (a) prove the selected original Bishop g=Log branch exists;
--   (b) prove each original normalized orbit's geometric increment
--       bound on a certified inverse-invariant disk;
--   (c) construct the selected nonreal exp fixed point p.
-- This module does not manufacture any of those sources.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)

import Real as BishopReal

import DASHI.Analysis.BishopComplexSeriesConvergenceExact as Complex
import DASHI.Analysis.BishopComplexAlgebraExact as Algebra
import DASHI.Moonshine.AbelBishopKoenigsFiniteTelescopingExact as Telescope
import DASHI.Moonshine.AbelBishopKoenigsGeometricAbsoluteExact as Geom
import DASHI.Moonshine.AbelBishopInverseKoenigsFiniteOrbitExact as Orbit
import DASHI.Moonshine.AbelBishopInverseKoenigsGeometricOrbitExact as Completion
import DASHI.Moonshine.AbelBishopInverseKoenigsSchroederLimitExact as Limit

originalBishopInverseKoenigsGeometricSchroeder :
  (p : Complex.BishopComplex) →
  (g : Complex.BishopComplex → Complex.BishopComplex) →
  (z : Complex.BishopComplex) →
  (constant ratio : BishopReal.ℝ) →
  (boundAtZ : Geom.OriginalBishopGeometricComponentBounds
    (Telescope.originalBishopComplexStepDifference
      (λ n → Orbit.inverseKoenigsPrefix p g n z))
    constant ratio) →
  (boundAtGZ : Geom.OriginalBishopGeometricComponentBounds
    (Telescope.originalBishopComplexStepDifference
      (λ n → Orbit.inverseKoenigsPrefix p g n (g z)))
    constant ratio) →
  Complex._≈C_
    (Algebra._*C_
      p
      (Completion.originalBishopInverseKoenigsGeometricLimit
        p g (g z) constant ratio boundAtGZ))
    (Completion.originalBishopInverseKoenigsGeometricLimit
      p g z constant ratio boundAtZ)
originalBishopInverseKoenigsGeometricSchroeder
  p g z constant ratio boundAtZ boundAtGZ =
  Limit.originalBishopInverseKoenigsLimitSchroeder
    p g z
    (Completion.originalBishopInverseKoenigsGeometricLimit
      p g z constant ratio boundAtZ)
    (Completion.originalBishopInverseKoenigsGeometricLimit
      p g (g z) constant ratio boundAtGZ)
    (Completion.originalBishopInverseKoenigsGeometricConverges
      p g z constant ratio boundAtZ)
    (Completion.originalBishopInverseKoenigsGeometricConverges
      p g (g z) constant ratio boundAtGZ)
