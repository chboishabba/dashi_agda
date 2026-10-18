{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YMClayMixedScalarPhysicalSpectrumExact where

------------------------------------------------------------------------
-- PHYSICAL SPECTRUM INTERPRETATION WITH INDEPENDENT CORRELATION SCALAR.
--
-- Energy/gap coordinates remain rational as required by the literal Clay
-- endpoint.  The connected-correlation carrier is arbitrary, so the actual
-- CMP119 real covariance can be used without identifying ℚ with ℝ.
------------------------------------------------------------------------

open import Data.Rational.Base using (ℚ)
open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanClayT5ClusteringToTransferGapExact as Gap
import DASHI.Physics.YangMills.BalabanOSMassGapClosure as OS

record MixedScalarPhysicalSpectrumInterpretation
    {Observable Bound Hamiltonian : Set}
    (spectrum : Gap.ReconstructedClusteringSpectrum Observable ℚ Bound)
    : Set₁ where
  field
    physicalHamiltonian : Hamiltonian
    SpectrumAboveVacuumGap : Hamiltonian → ℚ → Set

    noPositiveSubgapMeansSpectrumSeparated :
      Gap.NoPositiveSubgapMode spectrum →
      SpectrumAboveVacuumGap
        physicalHamiltonian
        (Gap.gapCandidate spectrum)

open MixedScalarPhysicalSpectrumInterpretation public

physicalMassGapCertificate :
  ∀ {Observable Bound Hamiltonian}
    {spectrum : Gap.ReconstructedClusteringSpectrum Observable ℚ Bound} →
  MixedScalarPhysicalSpectrumInterpretation
    {Hamiltonian = Hamiltonian} spectrum →
  Gap.PositiveTransferGapCore spectrum →
  OS.PhysicalMassGapCertificate Hamiltonian ℚ
physicalMassGapCertificate {spectrum = spectrum} interpretation core = record
  { OS.PhysicalMassGapCertificate.hamiltonian =
      physicalHamiltonian interpretation
  ; OS.PhysicalMassGapCertificate.gap =
      Gap.gapCandidate spectrum
  ; OS.PhysicalMassGapCertificate.Positive =
      Gap.PositiveEnergy spectrum
  ; OS.PhysicalMassGapCertificate.gapPositive =
      Gap.gapCandidatePositive core
  ; OS.PhysicalMassGapCertificate.SpectrumAboveVacuumGap =
      SpectrumAboveVacuumGap interpretation
  ; OS.PhysicalMassGapCertificate.spectrumAboveVacuumGap =
      noPositiveSubgapMeansSpectrumSeparated interpretation
        (Gap.noPositiveSubgapMode core)
  }

mixedScalarPhysicalSpectrumCompilerLevel : ProofLevel
mixedScalarPhysicalSpectrumCompilerLevel = machineChecked

mixedScalarPhysicalSpectrumInterpretationLevel : ProofLevel
mixedScalarPhysicalSpectrumInterpretationLevel = conditional
