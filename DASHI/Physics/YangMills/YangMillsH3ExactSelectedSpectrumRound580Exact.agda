{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsH3ExactSelectedSpectrumRound580Exact where

------------------------------------------------------------------------
-- GOAL-1 / ROUND580:
-- H3 DIRECTLY ON H2'S RECONSTRUCTION AND THE EXACT R281 SELECTED SOURCE.
--
-- The previous endpoint-facing H3 record still allowed an indexed-spectrum
-- object to choose its own R281 source and then asked for an equality back to
-- Direct.spectrumSource.  That equality is avoidable representation debt.
--
-- State the physical theorem directly on the exact selected R281 source and
-- H2's exact reconstruction.  The P3 indexed wrapper is then constructed with
-- source = Direct.spectrumSource definitionally.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.YangMillsClayLiteralTopDownConstructionExact as Top
import DASHI.Physics.YangMills.YangMillsDirectSourceOSSameHGapExact as Direct
import DASHI.Physics.YangMills.YangMillsDirectSourceOSRationalContinuumH2Exact as H2
import DASHI.Physics.YangMills.YangMillsDirectSourceOSReconstructedSpectrumH3Exact as H3
import DASHI.Physics.YangMills.YMClayLiteralWilsonP3SameOSCorrelationExact as P3
import DASHI.Physics.YangMills.BalabanContinuumCovarianceSpectrumConstructorRound281Exact as R281
import DASHI.Physics.YangMills.BalabanClayT5ClusteringToTransferGapExact as Gap
import DASHI.Physics.YangMills.BalabanOSMassGapClosure as OS
import DASHI.Physics.YangMills.YMClayR387PhysicalSpectrumExact as Spectrum

record ExactSelectedSpectrumOfH2Reconstruction
    {C : Top.LiteralYangMillsCarriers}
    {S : Top.LiteralYangMillsSemantics C}
    {Y : Top.LiteralYangMillsConstruction C S}
    (continuum : H2.RationalLiteralContinuumSameObjectBridge Y)
    {G : Top.CompactSimpleGroup C}
    (direct : Direct.LiteralGroupDirectSourceSameHGap Y G)
    : Set₂ where
  field
    SpectrumOfH2ReconstructedHamiltonian :
      OS.Hamiltonian (H2.reconstruction continuum G) →
      Gap.ReconstructedClusteringSpectrum (Top.Observable C) ℚ ℚ →
      Set

    exactSelectedR281SpectrumIsH2Reconstructed :
      SpectrumOfH2ReconstructedHamiltonian
        (OS.hamiltonian (H2.reconstruction continuum G))
        (R281.asReconstructedClusteringSpectrum
          (Direct.spectrumSource direct))

    selectedPhysicalHamiltonianIsH2Reconstructed :
      Spectrum.physicalHamiltonian (Direct.physicalSpectrum direct)
      ≡
      H2.hamiltonianToLiteral continuum G
        (OS.hamiltonian (H2.reconstruction continuum G))

open ExactSelectedSpectrumOfH2Reconstruction public

indexedSpectrum :
  ∀ {C S Y G}
    {continuum : H2.RationalLiteralContinuumSameObjectBridge
      {C = C} {S = S} Y}
    {direct : Direct.LiteralGroupDirectSourceSameHGap Y G} →
  ExactSelectedSpectrumOfH2Reconstruction continuum direct →
  P3.OSIndexedContinuumCovarianceSpectrum
    (H2.reconstruction continuum G)
    (Direct.dataSet direct)
    (Direct.extension direct)
    (Direct.tests direct)
indexedSpectrum {direct = direct} source = record
  { P3.OSIndexedContinuumCovarianceSpectrum.source =
      Direct.spectrumSource direct
  ; P3.OSIndexedContinuumCovarianceSpectrum.SpectrumOfReconstructedHamiltonian =
      SpectrumOfH2ReconstructedHamiltonian source
  ; P3.OSIndexedContinuumCovarianceSpectrum.spectrumOfReconstructedHamiltonian =
      exactSelectedR281SpectrumIsH2Reconstructed source
  }

asEndpointH3 :
  ∀ {C S Y G}
    {continuum : H2.RationalLiteralContinuumSameObjectBridge
      {C = C} {S = S} Y}
    {direct : Direct.LiteralGroupDirectSourceSameHGap Y G} →
  ExactSelectedSpectrumOfH2Reconstruction continuum direct →
  H3.LiteralSelectedSpectrumIsSameOSHamiltonian continuum direct
asEndpointH3 source = record
  { H3.LiteralSelectedSpectrumIsSameOSHamiltonian.indexedSpectrum =
      indexedSpectrum source
  ; H3.LiteralSelectedSpectrumIsSameOSHamiltonian.indexedSourceIsSelectedSource =
      refl
  ; H3.LiteralSelectedSpectrumIsSameOSHamiltonian.selectedPhysicalHamiltonianIsH2ReconstructedHamiltonian =
      selectedPhysicalHamiltonianIsH2Reconstructed source
  }

round580ExactSelectedSpectrumCompilerLevel : ProofLevel
round580ExactSelectedSpectrumCompilerLevel = machineChecked

-- H3 is now exactly two physical statements on fixed objects:
--   (1) the exact selected R281 spectrum is the spectral object of H2.reconstruction;
--   (2) the already-selected physical spectral Hamiltonian is that H2 Hamiltonian.
-- No independent R281 source equality remains.
round580ExactSelectedSpectrumPhysicalLevel : ProofLevel
round580ExactSelectedSpectrumPhysicalLevel = conditional
