module DASHI.Physics.YangMills.YangMillsFreeGaussianMaxwellNoGapExact where

------------------------------------------------------------------------
-- ROUND74: MASSLESS FREE/MAXWELL ONE-PARTICLE SECTOR HAS NO POSITIVE GAP
--
-- CALIBRATION / STANDARD SOURCES
--
-- James Glimm and Arthur Jaffe,
-- "Quantum Physics: A Functional Integral Point of View", 2nd ed., Springer,
-- 1987. DOI: 10.1007/978-1-4612-4728-9.
--
-- Stephen J. Gustafson and Israel Michael Sigal,
-- "Mathematical Concepts of Quantum Mechanics", Springer.
-- DOI: 10.1007/978-3-642-55729-3.
--
-- The standard free Maxwell/Fock Hamiltonian has massless one-particle
-- dispersion omega(p)=|p| on transverse modes.  Hence there are non-vacuum
-- one-particle states with arbitrarily small positive energy, and no interval
-- (0,m) can be free of spectrum for any m>0.
--
-- TOP-DOWN USE
--
-- The current Clay graph uses a strict finite fourth cumulant as an interaction
-- witness.  This file tests a potentially much cheaper alternative:
--
--   if a Gaussian/free continuum Yang--Mills theory with the required UV
--   normalization necessarily contains the massless Maxwell one-particle
--   sector, then the already-required positive physical mass gap rules out that
--   Gaussian/free possibility.
--
-- The spectral contradiction below is exact.  What remains physical is the
-- SAME-THEORY bridge
--
--   Gaussian/free YM + correct YM normalization
--       -> massless transverse Maxwell one-particle sector,
--
-- and the semantic identification
--
--   not free/Gaussian -> Clay's `IsNontrivialQuantumYangMills`.
--
-- Until those two bridges are proved, the fourth-cumulant route remains the
-- authoritative nontriviality producer; this module does not silently delete
-- theorem #8.
------------------------------------------------------------------------

open import DASHI.Physics.YangMills.CompactLieProofLevel

record GapOrder : Set₁ where
  field
    Energy : Set
    zero : Energy
    StrictLess : Energy → Energy → Set

open GapOrder public

record MasslessOneParticleApproximation (O : GapOrder) : Set₁ where
  field
    State : Set
    energy : State → Energy O
    NonVacuum : State → Set

    -- Arbitrarily small positive one-particle energies.
    stateBelowEveryPositiveThreshold : ∀ threshold →
      StrictLess O (zero O) threshold →
      State

    selectedNonVacuum : ∀ threshold positive →
      NonVacuum (stateBelowEveryPositiveThreshold threshold positive)

    selectedEnergyPositive : ∀ threshold positive →
      StrictLess O (zero O)
        (energy (stateBelowEveryPositiveThreshold threshold positive))

    selectedEnergyBelowThreshold : ∀ threshold positive →
      StrictLess O
        (energy (stateBelowEveryPositiveThreshold threshold positive))
        threshold

open MasslessOneParticleApproximation public

record PositiveSpectralGap
    {O : GapOrder}
    (massless : MasslessOneParticleApproximation O) : Set₁ where
  field
    gap : Energy O
    gapPositive : StrictLess O (zero O) gap

    -- Every non-vacuum state has energy at least the gap.  `NotBelow` is kept
    -- abstract so no total-order law is smuggled into the spectral argument.
    NotBelow : Energy O → Energy O → Set
    nonVacuumNotBelowGap : ∀ state →
      NonVacuum massless state →
      NotBelow (energy massless state) gap

    belowContradictsNotBelow : ∀ energy threshold →
      StrictLess O energy threshold →
      NotBelow energy threshold →
      SpectralContradiction

    SpectralContradiction : Set

open PositiveSpectralGap public

masslessSectorContradictsPositiveGap :
  ∀ {O} (massless : MasslessOneParticleApproximation O) →
  (gapData : PositiveSpectralGap massless) →
  SpectralContradiction gapData
masslessSectorContradictsPositiveGap massless gapData =
  let
    state = stateBelowEveryPositiveThreshold massless
      (gap gapData) (gapPositive gapData)
    below = selectedEnergyBelowThreshold massless
      (gap gapData) (gapPositive gapData)
    nonvacuum = selectedNonVacuum massless
      (gap gapData) (gapPositive gapData)
    notBelow = nonVacuumNotBelowGap gapData state nonvacuum
  in
  belowContradictsNotBelow gapData
    (energy massless state) (gap gapData) below notBelow

masslessOneParticleSectorHasNoPositiveGapLevel : ProofLevel
masslessOneParticleSectorHasNoPositiveGapLevel = machineChecked

freeMaxwellMasslessDispersionLevel : ProofLevel
freeMaxwellMasslessDispersionLevel = standardImported

-- Two exact top-down holes before this can replace the fourth-cumulant route.
physicalFreeGaussianYMContainsMasslessMaxwellSectorLevel : ProofLevel
physicalFreeGaussianYMContainsMasslessMaxwellSectorLevel = conditional

physicalNotFreeGaussianImpliesClayNontrivialityLevel : ProofLevel
physicalNotFreeGaussianImpliesClayNontrivialityLevel = conditional
