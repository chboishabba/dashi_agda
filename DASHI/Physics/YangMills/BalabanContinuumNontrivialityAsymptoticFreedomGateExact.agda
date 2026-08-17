module DASHI.Physics.YangMills.BalabanContinuumNontrivialityAsymptoticFreedomGateExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / WARNING
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
-- Michael Aizenman and Hugo Duminil-Copin,
-- "Marginal triviality of the scaling limits of critical 4D Ising and
-- phi^4_4 models", Annals of Mathematics 194 (2021), 163--235.
-- DOI: 10.4007/annals.2021.194.1.3.
-- Corrigendum: Annals of Mathematics 199 (2024), 479.
-- DOI: 10.4007/annals.2024.199.1.7.
--
-- DASHI CONTRIBUTION / EPISTEMIC BOUNDARY
--
-- The one-loop sign and the controlled five-channel g^4 remainder are not
-- side calculations: together they must leave a strictly positive physical
-- beta margin along the weak-coupling trajectory.  This file makes that
-- dependency executable.  It deliberately does NOT assert that positive beta
-- implies a non-Gaussian continuum limit.  The phi^4_4 triviality theorem is a
-- concrete warning that continuum interacting survival is an independent
-- theorem even after a beautiful cutoff construction exists.
------------------------------------------------------------------------

open import Data.Rational.Base as ℚ using (ℚ; _-_; _≤_; _<_)
import Data.Rational.Properties as ℚP

open import DASHI.Physics.YangMills.CompactLieProofLevel

record AsymptoticFreedomSurvivalMargin : Set where
  field
    oneLoopCoefficient : ℚ
    controlledHigherOrderPenalty : ℚ
    physicalBetaCoefficient : ℚ

    survivalMarginPositive :
      0ℚ < oneLoopCoefficient - controlledHigherOrderPenalty

    physicalBetaDominatesSurvivalMargin :
      oneLoopCoefficient - controlledHigherOrderPenalty
      ≤ physicalBetaCoefficient
open AsymptoticFreedomSurvivalMargin public

physicalBetaStrictlyPositive :
  ∀ data → 0ℚ < physicalBetaCoefficient data
physicalBetaStrictlyPositive data =
  ℚP.<-≤-trans
    (survivalMarginPositive data)
    (physicalBetaDominatesSurvivalMargin data)

asymptoticFreedomSurvivalMarginLevel : ProofLevel
asymptoticFreedomSurvivalMarginLevel = machineChecked

-- Physical B/C producers still required to instantiate the margin.
literalOneLoopPositiveMarginLevel : ProofLevel
literalOneLoopPositiveMarginLevel = conditional

literalFiveChannelPenaltyControlLevel : ProofLevel
literalFiveChannelPenaltyControlLevel = conditional

-- The continuum theorem remains independent: exhibit an actual gauge-invariant
-- non-Gaussian/interacting observable surviving the common continuum limit.
continuumYangMillsInteractingSurvivalLevel : ProofLevel
continuumYangMillsInteractingSurvivalLevel = conditional
