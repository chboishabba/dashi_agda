module DASHI.Physics.YangMills.BalabanClayT4BetaNormalizationConventionExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Integer.Base using (+_)
open import Data.Rational using (ℚ; _*_; _/_)
import Data.Rational.Tactic.RingSolver as ℚRing

open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Literature and convention ledger.
--
-- D. J. Gross and F. Wilczek,
-- "Ultraviolet Behavior of Non-Abelian Gauge Theories",
-- Physical Review Letters 30 (1973), 1343--1346.
-- DOI: 10.1103/PhysRevLett.30.1343
--
-- H. D. Politzer,
-- "Reliable Perturbative Results for Strong Interactions?",
-- Physical Review Letters 30 (1973), 1346--1349.
-- DOI: 10.1103/PhysRevLett.30.1346
--
-- R. Dashen and D. J. Gross,
-- "Relationship between lattice and continuum definitions of the gauge-theory
-- coupling",
-- Physical Review D 23 (1981), 2340--2348.
-- DOI: 10.1103/PhysRevD.23.2340
--
-- Fixed convention:
--
--   beta(g) = - [(11 C_A / 3) / (16 pi^2)] g^3 + higher order,
--
-- so
--
--   d(1/g^2)/d(log mu)
--     = 2 [(11 C_A / 3) / (16 pi^2)]
--     = (11 C_A)/(24 pi^2).
--
-- The frequently written beta_0/(8 pi^2) is the same coefficient when
-- beta_0 = 11 C_A / 3.  This module proves the rational part of that equality;
-- the common factor 1/pi^2 is deliberately kept outside the rational ledger.
------------------------------------------------------------------------

pureYMBetaZero : ℚ → ℚ
pureYMBetaZero casimirAdjoint = (+ 11 / 3) * casimirAdjoint

-- Rational coefficient multiplying 1/pi^2 in beta(g) = - coefficient * g^3.
pureYMBetaGCoefficient : ℚ → ℚ
pureYMBetaGCoefficient casimirAdjoint =
  pureYMBetaZero casimirAdjoint * (+ 1 / 16)

-- Rational coefficient multiplying 1/pi^2 in d(1/g^2)/d(log mu).
pureYMInverseCouplingCoefficient : ℚ → ℚ
pureYMInverseCouplingCoefficient casimirAdjoint =
  pureYMBetaZero casimirAdjoint * (+ 1 / 8)

solveBetaDerivative : ∀ b → (+ 2 / 1) * (b * (+ 1 / 16)) ≡ b * (+ 1 / 8)
solveBetaDerivative = ℚRing.solve-∀

inverseCouplingFromBetaDerivative : ∀ casimirAdjoint →
  (+ 2 / 1) * pureYMBetaGCoefficient casimirAdjoint
  ≡ pureYMInverseCouplingCoefficient casimirAdjoint
inverseCouplingFromBetaDerivative casimirAdjoint =
  solveBetaDerivative (pureYMBetaZero casimirAdjoint)

solveElevenOverTwentyFour : ∀ c → ((+ 11 / 3) * c) * (+ 1 / 8) ≡ (+ 11 / 24) * c
solveElevenOverTwentyFour = ℚRing.solve-∀

inverseCouplingIsElevenOverTwentyFour : ∀ casimirAdjoint →
  pureYMInverseCouplingCoefficient casimirAdjoint
  ≡ (+ 11 / 24) * casimirAdjoint
inverseCouplingIsElevenOverTwentyFour casimirAdjoint =
  solveElevenOverTwentyFour casimirAdjoint

solveBetaZeroOverEight : ∀ b → b * (+ 1 / 8) ≡ (+ 1 / 8) * b
solveBetaZeroOverEight = ℚRing.solve-∀

inverseCouplingIsBetaZeroOverEight : ∀ casimirAdjoint →
  pureYMInverseCouplingCoefficient casimirAdjoint
  ≡ (+ 1 / 8) * pureYMBetaZero casimirAdjoint
inverseCouplingIsBetaZeroOverEight casimirAdjoint =
  solveBetaZeroOverEight (pureYMBetaZero casimirAdjoint)

elevenCasimirConvention : ℚ → ℚ
elevenCasimirConvention casimirAdjoint = (+ 11 / 1) * casimirAdjoint

solveElevenConvention : ∀ c → (+ 1 / 24) * ((+ 11 / 1) * c) ≡ ((+ 11 / 3) * c) * (+ 1 / 8)
solveElevenConvention = ℚRing.solve-∀

inverseCouplingFromElevenConvention : ∀ casimirAdjoint →
  (+ 1 / 24) * elevenCasimirConvention casimirAdjoint
  ≡ pureYMInverseCouplingCoefficient casimirAdjoint
inverseCouplingFromElevenConvention casimirAdjoint =
  solveElevenConvention casimirAdjoint

record PureYMOneLoopConvention : Set where
  constructor pureYMConvention
  field
    casimirAdjoint : ℚ
    betaZero : ℚ
    betaGCoefficient : ℚ
    inverseCouplingCoefficient : ℚ

    betaZeroExact : betaZero ≡ pureYMBetaZero casimirAdjoint
    betaGCoefficientExact :
      betaGCoefficient ≡ pureYMBetaGCoefficient casimirAdjoint
    inverseCouplingCoefficientExact :
      inverseCouplingCoefficient ≡ pureYMInverseCouplingCoefficient casimirAdjoint

open PureYMOneLoopConvention public

canonicalPureYMOneLoopConvention : ℚ → PureYMOneLoopConvention
canonicalPureYMOneLoopConvention casimirAdjoint = pureYMConvention
  casimirAdjoint
  (pureYMBetaZero casimirAdjoint)
  (pureYMBetaGCoefficient casimirAdjoint)
  (pureYMInverseCouplingCoefficient casimirAdjoint)
  refl refl refl

betaDerivativeFactorOfTwoLevel : ProofLevel
betaDerivativeFactorOfTwoLevel = machineChecked

betaZeroOverEightEqualsElevenOverTwentyFourLevel : ProofLevel
betaZeroOverEightEqualsElevenOverTwentyFourLevel = machineChecked

pureYMWilsonConventionLedgerLevel : ProofLevel
pureYMWilsonConventionLedgerLevel = machineChecked

localizedPlaquetteCoefficientOfExactRGStep : ℚ → ℚ
localizedPlaquetteCoefficientOfExactRGStep casimirAdjoint =
  pureYMInverseCouplingCoefficient casimirAdjoint

-- The remaining physical theorem is to identify the localized plaquette
-- coefficient produced by the exact Wilson/Haar RG step with this convention
-- and with the Dashen--Gross lattice/continuum calibration.
physicalPlaquetteCoefficientIdentificationLevel : ProofLevel
physicalPlaquetteCoefficientIdentificationLevel = conditional
