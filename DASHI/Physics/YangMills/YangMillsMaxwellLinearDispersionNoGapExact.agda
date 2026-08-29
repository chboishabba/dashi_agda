module DASHI.Physics.YangMills.YangMillsMaxwellLinearDispersionNoGapExact where

------------------------------------------------------------------------
-- ROUND77: MASSLESS MAXWELL DISPERSION -> PHYSICAL GAP CONTRADICTION
--
-- PRIMARY / CALIBRATION SOURCES
--
-- E. Huguet and J. Renaud,
-- "Two-point function for the Maxwell field in flat Robertson-Walker
-- spacetimes", Physical Review D 88 (2013), 124018.
-- DOI: 10.1103/PhysRevD.88.124018.
--
-- James Glimm and Arthur Jaffe,
-- "Quantum Physics: A Functional Integral Point of View", 2nd ed., Springer,
-- 1987. DOI: 10.1007/978-1-4612-4728-9.
--
-- IMPORTANT ROUND77 CORRECTION
--
-- The Clay Hamiltonian acts on the physical/gauge-invariant Hilbert space. A
-- free colour gauge field need not contribute a single coloured one-particle
-- vector to that physical space. Therefore the Gaussian reductio must not rely
-- solely on a coloured one-particle state.
--
-- The standard free Maxwell/Fock theory supplies gauge-invariant composite
-- excitations (equivalently the colour-singlet two-particle continuum generated
-- by local curvature polynomials such as Tr F^2) with arbitrarily small positive
-- total energy. That is the safe physical no-gap object. The generic record
-- below packages exactly that property and compiles it into the older abstract
-- `MasslessOneParticleApproximation` consumer, whose theorem in fact uses only
-- non-vacuum states with arbitrarily small positive energy and does not inspect
-- particle number.
------------------------------------------------------------------------

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.YangMillsFreeGaussianMaxwellNoGapExact as Free

------------------------------------------------------------------------
-- Legacy labelled one-particle presentation (still useful for ordinary Maxwell).
------------------------------------------------------------------------

record LabelledLinearMasslessDispersion (O : Free.GapOrder) : Set₁ where
  field
    State : Set
    energy : State → Free.Energy O
    NonVacuum : State → Set

    stateBelowEveryPositiveThreshold : ∀ threshold →
      Free.StrictLess O (Free.zero O) threshold → State

    selectedNonVacuum : ∀ threshold positive →
      NonVacuum (stateBelowEveryPositiveThreshold threshold positive)

    selectedEnergyPositive : ∀ threshold positive →
      Free.StrictLess O (Free.zero O)
        (energy (stateBelowEveryPositiveThreshold threshold positive))

    selectedEnergyBelowThreshold : ∀ threshold positive →
      Free.StrictLess O
        (energy (stateBelowEveryPositiveThreshold threshold positive))
        threshold

open LabelledLinearMasslessDispersion public

labelledLinearDispersionGivesMasslessSector :
  ∀ {O} (dispersion : LabelledLinearMasslessDispersion O) →
  Free.MasslessOneParticleApproximation O
labelledLinearDispersionGivesMasslessSector dispersion = record
  { Free.MasslessOneParticleApproximation.State = State dispersion
  ; Free.MasslessOneParticleApproximation.energy = energy dispersion
  ; Free.MasslessOneParticleApproximation.NonVacuum = NonVacuum dispersion
  ; Free.MasslessOneParticleApproximation.stateBelowEveryPositiveThreshold =
      stateBelowEveryPositiveThreshold dispersion
  ; Free.MasslessOneParticleApproximation.selectedNonVacuum =
      selectedNonVacuum dispersion
  ; Free.MasslessOneParticleApproximation.selectedEnergyPositive =
      selectedEnergyPositive dispersion
  ; Free.MasslessOneParticleApproximation.selectedEnergyBelowThreshold =
      selectedEnergyBelowThreshold dispersion
  }

labelledLinearDispersionContradictsPositiveGap :
  ∀ {O}
    (dispersion : LabelledLinearMasslessDispersion O) →
    (gapData : Free.PositiveSpectralGap
      (labelledLinearDispersionGivesMasslessSector dispersion)) →
  Free.SpectralContradiction gapData
labelledLinearDispersionContradictsPositiveGap dispersion gapData =
  Free.masslessSectorContradictsPositiveGap
    (labelledLinearDispersionGivesMasslessSector dispersion)
    gapData

------------------------------------------------------------------------
-- Clay-safe physical version: every selected low-energy state is explicitly
-- gauge invariant. Nothing in the no-gap compiler relies on particle number.
------------------------------------------------------------------------

record GaplessGaugeInvariantPhysicalSector (O : Free.GapOrder) : Set₁ where
  field
    State : Set
    energy : State → Free.Energy O
    NonVacuum : State → Set
    GaugeInvariantPhysical : State → Set

    stateBelowEveryPositiveThreshold : ∀ threshold →
      Free.StrictLess O (Free.zero O) threshold → State

    selectedNonVacuum : ∀ threshold positive →
      NonVacuum (stateBelowEveryPositiveThreshold threshold positive)

    selectedGaugeInvariantPhysical : ∀ threshold positive →
      GaugeInvariantPhysical
        (stateBelowEveryPositiveThreshold threshold positive)

    selectedEnergyPositive : ∀ threshold positive →
      Free.StrictLess O (Free.zero O)
        (energy (stateBelowEveryPositiveThreshold threshold positive))

    selectedEnergyBelowThreshold : ∀ threshold positive →
      Free.StrictLess O
        (energy (stateBelowEveryPositiveThreshold threshold positive))
        threshold

open GaplessGaugeInvariantPhysicalSector public

gaugeInvariantPhysicalSectorGivesGaplessApproximation :
  ∀ {O} (sector : GaplessGaugeInvariantPhysicalSector O) →
  Free.MasslessOneParticleApproximation O
gaugeInvariantPhysicalSectorGivesGaplessApproximation sector = record
  { Free.MasslessOneParticleApproximation.State = State sector
  ; Free.MasslessOneParticleApproximation.energy = energy sector
  ; Free.MasslessOneParticleApproximation.NonVacuum = NonVacuum sector
  ; Free.MasslessOneParticleApproximation.stateBelowEveryPositiveThreshold =
      stateBelowEveryPositiveThreshold sector
  ; Free.MasslessOneParticleApproximation.selectedNonVacuum =
      selectedNonVacuum sector
  ; Free.MasslessOneParticleApproximation.selectedEnergyPositive =
      selectedEnergyPositive sector
  ; Free.MasslessOneParticleApproximation.selectedEnergyBelowThreshold =
      selectedEnergyBelowThreshold sector
  }

gaugeInvariantPhysicalSectorContradictsPositiveGap :
  ∀ {O}
    (sector : GaplessGaugeInvariantPhysicalSector O) →
    (gapData : Free.PositiveSpectralGap
      (gaugeInvariantPhysicalSectorGivesGaplessApproximation sector)) →
  Free.SpectralContradiction gapData
gaugeInvariantPhysicalSectorContradictsPositiveGap sector gapData =
  Free.masslessSectorContradictsPositiveGap
    (gaugeInvariantPhysicalSectorGivesGaplessApproximation sector)
    gapData

maxwellLinearDispersionSourceLevel : ProofLevel
maxwellLinearDispersionSourceLevel = standardImported

-- Standard free/Fock fact used by the Clay reductio: after Maxwell-kernel
-- identification, gauge-invariant curvature composites have spectral support
-- accumulating at zero (a colour-singlet two-particle continuum suffices).
freeMaxwellGaugeInvariantGaplessSectorLevel : ProofLevel
freeMaxwellGaugeInvariantGaplessSectorLevel = standardImported

labelledDispersionToNoGapCompilerLevel : ProofLevel
labelledDispersionToNoGapCompilerLevel = machineChecked

gaugeInvariantPhysicalSectorToNoGapCompilerLevel : ProofLevel
gaugeInvariantPhysicalSectorToNoGapCompilerLevel = machineChecked

-- The physical seam after Round77 is no longer "find a coloured one-particle
-- state". It is the same-family Gaussian/Ward -> Maxwell kernel identification;
-- standard free-field reconstruction then supplies the gauge-invariant gapless
-- composite sector consumed above.
physicalGaussianYMToGaugeInvariantMaxwellSectorLevel : ProofLevel
physicalGaussianYMToGaugeInvariantMaxwellSectorLevel = conditional
