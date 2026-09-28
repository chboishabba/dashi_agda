{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsDirectSourceOSReconstructedSpectrumH3Exact where

------------------------------------------------------------------------
-- H3: THE SELECTED R281 SPECTRUM IS THE SAME OS-RECONSTRUCTED HAMILTONIAN.
--
-- R281 already makes
--
--   selected continuum covariance = connected spectral correlation
--
-- definitional.  P3 correctly isolates the only physical payment: that this
-- exact spectrum is the spectral object of the actual OS reconstruction.
--
-- This owner attaches that P3 theorem to the exact per-group H1/H2 carrier and
-- then welds both the source OS Schwinger system and reconstructed Hamiltonian
-- to the literal endpoint Y.  No auxiliary transfer Hamiltonian is introduced.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational.Base using (ℚ)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.YangMillsClayLiteralTopDownConstructionExact as Top
import DASHI.Physics.YangMills.YangMillsDirectSourceOSSameHGapExact as Direct
import DASHI.Physics.YangMills.BalabanOSMassGapClosure as OS
import DASHI.Physics.YangMills.YMClayLiteralWilsonP3SameOSCorrelationExact as P3
import DASHI.Physics.YangMills.BalabanContinuumCovarianceSpectrumConstructorRound281Exact as R281
import DASHI.Physics.YangMills.YMClayR387PhysicalSpectrumExact as Spectrum

record LiteralSelectedSpectrumIsSameOSHamiltonian
    {C : Top.LiteralYangMillsCarriers}
    {S : Top.LiteralYangMillsSemantics C}
    {Y : Top.LiteralYangMillsConstruction C S}
    {G : Top.CompactSimpleGroup C}
    (direct :
      Direct.LiteralGroupDirectSourceSameHGap
        {C = C} {S = S} Y G)
    : Set₂ where
  field
    Point : Set

    sourceOSSystem :
      OS.ContinuumSchwingerSystem
        (Top.Observable C) Point ℚ

    reconstruction :
      OS.OSReconstructionAuthority
        (Top.Observable C) Point ℚ
        sourceOSSystem

    indexedSpectrum :
      P3.OSIndexedContinuumCovarianceSpectrum
        {SpectralObservable = Top.Observable C}
        {Energy = ℚ}
        reconstruction
        (Direct.dataSet direct)
        (Direct.extension direct)
        (Direct.tests direct)

    indexedSourceIsSelectedSource :
      P3.source indexedSpectrum
      ≡ Direct.spectrumSource direct

    sourceSystemToLiteralSchwinger :
      OS.ContinuumSchwingerSystem
        (Top.Observable C) Point ℚ →
      Top.SchwingerFamily C

    sourceOSSystemIsLiteralSchwinger :
      sourceSystemToLiteralSchwinger sourceOSSystem
      ≡ Top.schwinger Y G

    hamiltonianToLiteral :
      OS.Hamiltonian reconstruction →
      Top.Hamiltonian C

    reconstructedHamiltonianIsLiteral :
      hamiltonianToLiteral
        (OS.hamiltonian reconstruction)
      ≡ Top.hamiltonian Y G

    selectedPhysicalHamiltonianIsReconstructedHamiltonian :
      Spectrum.physicalHamiltonian
        (Direct.physicalSpectrum direct)
      ≡
      hamiltonianToLiteral
        (OS.hamiltonian reconstruction)

open LiteralSelectedSpectrumIsSameOSHamiltonian public

selectedSpectrumIsOSReconstructed :
  ∀ {C S Y G direct}
    (sameOS :
      LiteralSelectedSpectrumIsSameOSHamiltonian
        {C = C} {S = S} {Y = Y} {G = G} direct) →
  P3.SpectrumOfReconstructedHamiltonian
    (P3.indexedSpectrum sameOS)
    (OS.hamiltonian (reconstruction sameOS))
    (R281.asReconstructedClusteringSpectrum
      (Direct.spectrumSource direct))
selectedSpectrumIsOSReconstructed sameOS
  rewrite indexedSourceIsSelectedSource sameOS =
  P3.spectrumOfReconstructedHamiltonian
    (indexedSpectrum sameOS)

directH3SameOSCompilerLevel : ProofLevel
directH3SameOSCompilerLevel = machineChecked

-- H3 physical payment is now exactly the P3 reconstructed-spectrum theorem
-- plus the two same-object endpoint welds above.  The covariance/correlation
-- equality itself remains definitional in R281.
directH3SameOSPhysicalInstantiationLevel : ProofLevel
directH3SameOSPhysicalInstantiationLevel = conditional
