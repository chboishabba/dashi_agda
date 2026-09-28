{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsDirectSourceOSReconstructedSpectrumH3Exact where

------------------------------------------------------------------------
-- H3: THE SELECTED R281 SPECTRUM IS THE EXACT H2 OS RECONSTRUCTION.
--
-- H2 constructs one rational-valued continuum Schwinger system from the actual
-- finite family and one OS reconstruction of that system.  H3 does not choose
-- another system, another reconstruction, or another Hamiltonian.
--
-- R281 already makes selected continuum covariance = connected spectral
-- correlation definitional.  The remaining physical theorem is therefore that
-- this exact R281 spectrum is the reconstructed spectral object of H2's exact
-- OS reconstruction, together with the same-object identification between the
-- physical spectral Hamiltonian used by the gap certificate and H2's literal
-- reconstructed Hamiltonian.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational.Base using (ℚ)
open import Relation.Binary.PropositionalEquality using (trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.YangMillsClayLiteralTopDownConstructionExact as Top
import DASHI.Physics.YangMills.YangMillsDirectSourceOSSameHGapExact as Direct
import DASHI.Physics.YangMills.YangMillsDirectSourceOSRationalContinuumH2Exact as H2
import DASHI.Physics.YangMills.BalabanOSMassGapClosure as OS
import DASHI.Physics.YangMills.YMClayLiteralWilsonP3SameOSCorrelationExact as P3
import DASHI.Physics.YangMills.BalabanContinuumCovarianceSpectrumConstructorRound281Exact as R281
import DASHI.Physics.YangMills.YMClayR387PhysicalSpectrumExact as Spectrum

record LiteralSelectedSpectrumIsSameOSHamiltonian
    {C : Top.LiteralYangMillsCarriers}
    {S : Top.LiteralYangMillsSemantics C}
    {Y : Top.LiteralYangMillsConstruction C S}
    (continuum : H2.RationalLiteralContinuumSameObjectBridge Y)
    {G : Top.CompactSimpleGroup C}
    (direct :
      Direct.LiteralGroupDirectSourceSameHGap
        {C = C} {S = S} Y G)
    : Set₂ where
  field
    indexedSpectrum :
      P3.OSIndexedContinuumCovarianceSpectrum
        {SpectralObservable = Top.Observable C}
        {Energy = ℚ}
        (H2.reconstruction continuum G)
        (Direct.dataSet direct)
        (Direct.extension direct)
        (Direct.tests direct)

    indexedSourceIsSelectedSource :
      P3.source indexedSpectrum
      ≡ Direct.spectrumSource direct

    selectedPhysicalHamiltonianIsH2ReconstructedHamiltonian :
      Spectrum.physicalHamiltonian
        (Direct.physicalSpectrum direct)
      ≡
      H2.hamiltonianToLiteral continuum G
        (OS.hamiltonian (H2.reconstruction continuum G))

open LiteralSelectedSpectrumIsSameOSHamiltonian public

selectedSpectrumIsOSReconstructed :
  ∀ {C S}
    {Y : Top.LiteralYangMillsConstruction C S}
    {G : Top.CompactSimpleGroup C}
    {continuum : H2.RationalLiteralContinuumSameObjectBridge Y}
    {direct :
      Direct.LiteralGroupDirectSourceSameHGap
        {C = C} {S = S} Y G} →
  (sameOS :
    LiteralSelectedSpectrumIsSameOSHamiltonian continuum direct) →
  P3.SpectrumOfReconstructedHamiltonian
    (indexedSpectrum sameOS)
    (OS.hamiltonian (H2.reconstruction continuum G))
    (R281.asReconstructedClusteringSpectrum
      (Direct.spectrumSource direct))
selectedSpectrumIsOSReconstructed sameOS
  rewrite indexedSourceIsSelectedSource sameOS =
  P3.spectrumOfReconstructedHamiltonian
    (indexedSpectrum sameOS)

h2ReconstructedHamiltonianIsLiteral :
  ∀ {C S}
    {Y : Top.LiteralYangMillsConstruction C S}
    {G : Top.CompactSimpleGroup C}
    {continuum : H2.RationalLiteralContinuumSameObjectBridge Y}
    {direct :
      Direct.LiteralGroupDirectSourceSameHGap
        {C = C} {S = S} Y G} →
  (sameOS :
    LiteralSelectedSpectrumIsSameOSHamiltonian continuum direct) →
  H2.hamiltonianToLiteral continuum G
    (OS.hamiltonian (H2.reconstruction continuum G))
  ≡
  Top.hamiltonian Y G
h2ReconstructedHamiltonianIsLiteral {G = G} {continuum = continuum} sameOS =
  H2.reconstructedHamiltonianMeansLiteral continuum G

selectedPhysicalHamiltonianIsLiteral :
  ∀ {C S}
    {Y : Top.LiteralYangMillsConstruction C S}
    {G : Top.CompactSimpleGroup C}
    {continuum : H2.RationalLiteralContinuumSameObjectBridge Y}
    {direct :
      Direct.LiteralGroupDirectSourceSameHGap
        {C = C} {S = S} Y G} →
  (sameOS :
    LiteralSelectedSpectrumIsSameOSHamiltonian continuum direct) →
  Spectrum.physicalHamiltonian (Direct.physicalSpectrum direct)
  ≡ Top.hamiltonian Y G
selectedPhysicalHamiltonianIsLiteral {G = G} {continuum = continuum} sameOS =
  trans
    (selectedPhysicalHamiltonianIsH2ReconstructedHamiltonian sameOS)
    (H2.reconstructedHamiltonianMeansLiteral continuum G)

directH3SameOSCompilerLevel : ProofLevel
directH3SameOSCompilerLevel = machineChecked

-- H3 physical payment is now exactly:
--   * P3's reconstructed-spectrum theorem on H2's exact OS reconstruction;
--   * selected physical spectral Hamiltonian = H2 reconstructed Hamiltonian.
-- The H2 reconstruction -> literal Y Hamiltonian equality is already owned by
-- the continuum same-object bridge; no second OS/Hamiltonian selector remains.
directH3SameOSPhysicalInstantiationLevel : ProofLevel
directH3SameOSPhysicalInstantiationLevel = conditional
