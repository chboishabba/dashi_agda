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

    stateBelowEveryPositiveThreshold : ∀ threshold →
      StrictLess O (zero O) threshold → State

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
    SpectralContradiction : Set

    gap : Energy O
    gapPositive : StrictLess O (zero O) gap

    NotBelow : Energy O → Energy O → Set
    nonVacuumNotBelowGap : ∀ state →
      NonVacuum massless state →
      NotBelow (energy massless state) gap

    belowContradictsNotBelow : ∀ energy threshold →
      StrictLess O energy threshold →
      NotBelow energy threshold →
      SpectralContradiction

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

------------------------------------------------------------------------
-- Constructive Gaussian -> contradiction compiler.
------------------------------------------------------------------------

record GaussianMaxwellGapObstruction (O : GapOrder) : Set₁ where
  field
    Gaussian Contradiction : Set

    -- The SAME continuum theory, under a Gaussian/free hypothesis, exposes the
    -- standard massless transverse one-particle sector.
    masslessSector : Gaussian → MasslessOneParticleApproximation O

    -- The already-proved physical gap is transported to that same Hamiltonian.
    gapOnSector : ∀ gaussian → PositiveSpectralGap (masslessSector gaussian)

    -- The spectral contradiction type carried by the gap certificate is the
    -- contradiction type used to negate Gaussianity.
    contradictionFromSpectral : ∀ gaussian →
      SpectralContradiction (gapOnSector gaussian) → Contradiction

open GaussianMaxwellGapObstruction public

gaussianContradictsPositiveGap :
  ∀ {O} (dataSet : GaussianMaxwellGapObstruction O) →
  Gaussian dataSet → Contradiction dataSet
gaussianContradictsPositiveGap dataSet gaussian =
  contradictionFromSpectral dataSet gaussian
    (masslessSectorContradictsPositiveGap
      (masslessSector dataSet gaussian)
      (gapOnSector dataSet gaussian))

masslessOneParticleSectorHasNoPositiveGapLevel : ProofLevel
masslessOneParticleSectorHasNoPositiveGapLevel = machineChecked

gaussianGapContradictionCompilerLevel : ProofLevel
gaussianGapContradictionCompilerLevel = machineChecked

freeMaxwellMasslessDispersionLevel : ProofLevel
freeMaxwellMasslessDispersionLevel = standardImported

-- TRUE physical seam for the cheaper #8 route: prove the SAME reconstructed
-- continuum Yang--Mills system, if Gaussian/free, has the massless Maxwell
-- one-particle sector and that the already-produced physical gap is the gap on
-- that same Hamiltonian.  The logical contradiction thereafter is exact.
physicalFreeGaussianYMContainsMasslessMaxwellSectorLevel : ProofLevel
physicalFreeGaussianYMContainsMasslessMaxwellSectorLevel = conditional
