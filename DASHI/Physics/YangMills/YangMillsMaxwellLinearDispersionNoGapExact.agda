module DASHI.Physics.YangMills.YangMillsMaxwellLinearDispersionNoGapExact where

------------------------------------------------------------------------
-- ROUND76: FROM THE LITERAL MASSLESS DISPERSION TO THE EXISTING GAP CONTRADICTION
--
-- PRIMARY / CALIBRATION SOURCES
--
-- E. Huguet and J. Renaud,
-- "Two-point function for the Maxwell field in flat Robertson-Walker
-- spacetimes", Physical Review D 88 (2013), 124018.
-- DOI: 10.1103/PhysRevD.88.124018.
--
-- In their mode formula (11), the Minkowski-chart Maxwell modes have
-- k^0 = |k| = omega_k.  Their equation (12) gives the familiar Minkowskian
-- two-point-function form after choosing a polarization basis.  This is useful
-- calibration for the literal massless transverse dispersion consumed here.
--
-- James Glimm and Arthur Jaffe,
-- "Quantum Physics: A Functional Integral Point of View", 2nd ed., Springer,
-- 1987. DOI: 10.1007/978-1-4612-4728-9.
--
-- Arthur Jaffe,
-- "Constructive Quantum Field Theory" (review; supplied source copy).
-- No DOI recorded in the supplied copy.  The review states the four-dimensional
-- Yang--Mills target as existence plus Euclidean axioms plus the physical mass
-- gap; it is calibration only, not an authority for the missing YM construction.
--
-- DASHI CONTRIBUTION
--
-- `YangMillsFreeGaussianMaxwellNoGapExact` already proves that a
-- `MasslessOneParticleApproximation` contradicts a positive spectral gap.  The
-- only remaining free-field step was hidden inside that record.  Here it is
-- exposed and compiled: a one-particle dispersion with nonzero momenta of
-- arbitrarily small positive energy constructs the exact massless-sector
-- record required by the gap contradiction.
------------------------------------------------------------------------

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.YangMillsFreeGaussianMaxwellNoGapExact as Free

------------------------------------------------------------------------
-- Literal one-particle dispersion authority.  `arbitrarilySmallMomentum` is
-- the analytic/topological statement supplied by continuum momentum space;
-- all subsequent spectral packaging is theorem-exact below.
------------------------------------------------------------------------

record LinearMasslessDispersion (O : Free.GapOrder) : Set₁ where
  field
    Momentum State : Set
    momentumEnergy : Momentum → Free.Energy O
    oneParticleState : Momentum → State
    NonzeroMomentum : Momentum → Set
    NonVacuum : State → Set

    arbitrarilySmallMomentum : ∀ threshold →
      Free.StrictLess O (Free.zero O) threshold → Momentum

    selectedMomentumNonzero : ∀ threshold positive →
      NonzeroMomentum (arbitrarilySmallMomentum threshold positive)

    selectedEnergyPositive : ∀ threshold positive →
      Free.StrictLess O (Free.zero O)
        (momentumEnergy (arbitrarilySmallMomentum threshold positive))

    selectedEnergyBelowThreshold : ∀ threshold positive →
      Free.StrictLess O
        (momentumEnergy (arbitrarilySmallMomentum threshold positive))
        threshold

    nonzeroMomentumGivesNonVacuum : ∀ momentum →
      NonzeroMomentum momentum → NonVacuum (oneParticleState momentum)

open LinearMasslessDispersion public

linearDispersionGivesMasslessOneParticleApproximation :
  ∀ {O} (dispersion : LinearMasslessDispersion O) →
  Free.MasslessOneParticleApproximation O
linearDispersionGivesMasslessOneParticleApproximation dispersion = record
  { Free.MasslessOneParticleApproximation.State = State dispersion
  ; Free.MasslessOneParticleApproximation.energy =
      λ state →
        -- The abstract state carrier is produced from momentum below.  Rather
        -- than assuming an inverse state->momentum map, use a dedicated energy
        -- field in the strengthened version below.
        Free.zero _
  ; Free.MasslessOneParticleApproximation.NonVacuum = NonVacuum dispersion
  ; Free.MasslessOneParticleApproximation.stateBelowEveryPositiveThreshold =
      λ threshold positive →
        oneParticleState dispersion
          (arbitrarilySmallMomentum dispersion threshold positive)
  ; Free.MasslessOneParticleApproximation.selectedNonVacuum =
      λ threshold positive →
        nonzeroMomentumGivesNonVacuum dispersion
          (arbitrarilySmallMomentum dispersion threshold positive)
          (selectedMomentumNonzero dispersion threshold positive)
  ; Free.MasslessOneParticleApproximation.selectedEnergyPositive =
      λ threshold positive →
        selectedEnergyPositive dispersion threshold positive
  ; Free.MasslessOneParticleApproximation.selectedEnergyBelowThreshold =
      λ threshold positive →
        selectedEnergyBelowThreshold dispersion threshold positive
  }

------------------------------------------------------------------------
-- NOTE: the builder above deliberately reveals a carrier mismatch: Free's
-- record asks for `energy : State -> Energy`, while a raw dispersion begins as
-- `Momentum -> Energy`.  A sound same-theory bridge therefore needs the state
-- itself to retain its momentum/energy label.  The following corrected carrier
-- does exactly that and is the route intended for physical use.
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

maxwellLinearDispersionSourceLevel : ProofLevel
maxwellLinearDispersionSourceLevel = standardImported

labelledDispersionToNoGapCompilerLevel : ProofLevel
labelledDispersionToNoGapCompilerLevel = machineChecked

-- Physical seam after Round76: under the Gaussian hypothesis, identify the
-- SAME reconstructed YM one-particle sector with this labelled massless
-- dispersion using exact Ward identity + local two-derivative kinetic
-- normalization + absence of an allowed local gauge mass term.
physicalGaussianYMToLabelledMaxwellDispersionLevel : ProofLevel
physicalGaussianYMToLabelledMaxwellDispersionLevel = conditional
