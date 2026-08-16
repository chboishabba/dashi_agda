module DASHI.Moonshine.Hecke23AntiparallelExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Jean-Pierre Serre,
-- "A Course in Arithmetic", Graduate Texts in Mathematics 7,
-- Springer, 1973.
-- DOI: 10.1007/978-1-4684-9884-4.
--
-- DASHI CONTRIBUTION
--
-- The supplied finite Aristotle coefficient lane observes
--
--   t2(m) = -24 * tau(m)
--   t3(m) = 252 * tau(m).
--
-- Instead of introducing division to state t2/t3=-2/21, prove the stronger
-- integral cross-multiplied identity for every integer coefficient x:
--
--   21 * (-24 x) = (-2) * (252 x).
--
-- Hence any finite coefficient family instantiated by the supplied formulas is
-- exactly antiparallel, including zero coefficients, with no side condition
-- about division by zero.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Integer using (ℤ; +_; -[1+_]; _*_)
open import Data.Integer.Solver using (module +-*-Solver)
open +-*-Solver

hecke2ScaledCoefficient : ℤ → ℤ
hecke2ScaledCoefficient x = -[1+ 23 ] * x

hecke3ScaledCoefficient : ℤ → ℤ
hecke3ScaledCoefficient x = + 252 * x

hecke23AntiparallelCrossMultiplied :
  (x : ℤ) →
  (+ 21) * hecke2ScaledCoefficient x
  ≡ (-[1+ 1 ]) * hecke3ScaledCoefficient x
hecke23AntiparallelCrossMultiplied =
  solve 1
    (λ x →
      con (+ 21) :* (con (-[1+ 23 ]) :* x)
      :=
      con (-[1+ 1 ]) :* (con (+ 252) :* x))
    refl
