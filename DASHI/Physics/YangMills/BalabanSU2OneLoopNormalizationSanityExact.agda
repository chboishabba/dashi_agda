module DASHI.Physics.YangMills.BalabanSU2OneLoopNormalizationSanityExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- David J. Gross and Frank Wilczek,
-- "Ultraviolet Behavior of Non-Abelian Gauge Theories",
-- Physical Review Letters 30 (1973), 1343--1346.
-- DOI: 10.1103/PhysRevLett.30.1343.
--
-- H. David Politzer,
-- "Reliable Perturbative Results for Strong Interactions?",
-- Physical Review Letters 30 (1973), 1346--1349.
-- DOI: 10.1103/PhysRevLett.30.1346.
--
-- R. Dashen and D. J. Gross,
-- "Relationship between lattice and continuum definitions of the gauge-theory
-- coupling", Physical Review D 23 (1981), 2340--2348.
-- DOI: 10.1103/PhysRevD.23.2340.
--
-- DASHI CONTRIBUTION
--
-- Pin the exact SU(2) normalization target before the physical four-orbit
-- Wilson/ghost/Haar evaluation is intervalized.
--
-- The repository convention is
--
--   beta_0(G) = (11/3) C_A(G),
--
-- and the canonical SU(2) adjoint Casimir is C_A=2.  Therefore
--
--   beta_0(SU2) = 22/3.
--
-- For the repository's inverse-coupling flow
--
--   d(1/g^2)/d log(mu) = [beta_0/(8 pi^2)] + ...,
--
-- the rational coefficient multiplying 1/pi^2 is consequently 11/12.
--
-- This file is a normalization regression only.  It does not assert that the
-- current physical four-orbit expression has already been identified with, or
-- enclosed around, these values.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base using (ℚ; _/_)
import Data.Rational.Tactic.RingSolver as ℚRing

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayT4WilsonOneLoopConventionExact as Wilson
import DASHI.Physics.YangMills.BalabanClayT4BetaNormalizationConventionExact as Beta

su2BetaZero : ℚ
su2BetaZero = + 22 / 3

su2InverseCouplingCoefficient : ℚ
su2InverseCouplingCoefficient = + 11 / 12

su2BetaZeroExact :
  Beta.pureYMBetaZero Wilson.adjointCasimirSU2 ≡ su2BetaZero
su2BetaZeroExact = ℚRing.solve []

su2InverseCouplingCoefficientExact :
  Beta.pureYMInverseCouplingCoefficient Wilson.adjointCasimirSU2
  ≡ su2InverseCouplingCoefficient
su2InverseCouplingCoefficientExact = ℚRing.solve []

su2InverseCouplingFromBetaZeroExact :
  (+ 1 / 8) * su2BetaZero ≡ su2InverseCouplingCoefficient
su2InverseCouplingFromBetaZeroExact = ℚRing.solve []

su2OneLoopBetaNormalizationSanityLevel : ProofLevel
su2OneLoopBetaNormalizationSanityLevel = machineChecked

su2OneLoopInverseCouplingNormalizationSanityLevel : ProofLevel
su2OneLoopInverseCouplingNormalizationSanityLevel = machineChecked

-- Future physical one-loop work should prove that the literal four-orbit
-- Wilson + reduced-ghost + Haar scalar, after the already-declared CMP109/
-- Dashen--Gross normalization map, encloses this same coefficient.  Positivity
-- alone is necessary but a mismatched value would expose a convention error.
su2PhysicalFourOrbitNormalizationIdentificationLevel : ProofLevel
su2PhysicalFourOrbitNormalizationIdentificationLevel = conditional
