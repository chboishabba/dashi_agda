module DASHI.Physics.YangMills.YMClayR387PhysicalSpectrumExact where

------------------------------------------------------------------------
-- R387 / PHYSICAL SPECTRAL INTERPRETATION
--
-- The current Agda source lane already constructs a PositiveTransferGapCore on
-- the same continuum covariance carrier.  What it does not contain is a
-- physical Hamiltonian.  Lean calls this missing attachment a
-- `SpectralRepresentation`.
--
-- This owner makes exactly that seam explicit and no stronger: fix the physical
-- Hamiltonian and prove that the already-constructed absence of positive
-- subgap modes is the physical spectral-separation predicate for that same
-- Hamiltonian and the same rational gap candidate.  The physical mass-gap
-- certificate is then constructed rather than supplied as another hypothesis.
------------------------------------------------------------------------

open import Data.Rational.Base as ℚ using (ℚ)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram
import DASHI.Physics.YangMills.BalabanConnectedCovarianceExpectationLimitRound278Exact as R278
import DASHI.Physics.YangMills.BalabanT5UnlocalizedJSourceLocalizationRound318Exact as R318
import DASHI.Physics.YangMills.BalabanContinuumCovarianceSpectrumConstructorRound281Exact as R281
import DASHI.Physics.YangMills.BalabanCMP116R281SourceResponseSameObjectRound342Exact as R342
import DASHI.Physics.YangMills.BalabanCMP116DirectSelectedSpectralUpperRound387Exact as R387
import DASHI.Physics.YangMills.BalabanClayT5ClusteringToTransferGapExact as Gap
import DASHI.Physics.YangMills.BalabanDirectSelectedUpperToGapFinalExact as Final
import DASHI.Physics.YangMills.BalabanOSMassGapClosure as OSGap

record PhysicalSpectrumInterpretation
    {Observable Hamiltonian : Set}
    (spectrum : Gap.ReconstructedClusteringSpectrum Observable ℚ ℚ) : Set₁ where
  field
    physicalHamiltonian : Hamiltonian
    SpectrumAboveVacuumGap : Hamiltonian → ℚ → Set

    noPositiveSubgapMeansSpectrumSeparated :
      Gap.NoPositiveSubgapMode spectrum →
      SpectrumAboveVacuumGap
        physicalHamiltonian (Gap.gapCandidate spectrum)

open PhysicalSpectrumInterpretation public

physicalMassGapCertificateFromTransferGapCore :
  ∀ {Observable Hamiltonian}
    {spectrum : Gap.ReconstructedClusteringSpectrum Observable ℚ ℚ} →
  PhysicalSpectrumInterpretation {Hamiltonian = Hamiltonian} spectrum →
  Gap.PositiveTransferGapCore spectrum →
  OSGap.PhysicalMassGapCertificate Hamiltonian ℚ
physicalMassGapCertificateFromTransferGapCore interpretation core = record
  { OSGap.PhysicalMassGapCertificate.hamiltonian =
      physicalHamiltonian interpretation
  ; OSGap.PhysicalMassGapCertificate.gap = Gap.gapCandidate _
  ; OSGap.PhysicalMassGapCertificate.Positive = Gap.PositiveEnergy _
  ; OSGap.PhysicalMassGapCertificate.gapPositive =
      Gap.gapCandidatePositive core
  ; OSGap.PhysicalMassGapCertificate.SpectrumAboveVacuumGap =
      SpectrumAboveVacuumGap interpretation
  ; OSGap.PhysicalMassGapCertificate.spectrumAboveVacuumGap =
      noPositiveSubgapMeansSpectrumSeparated interpretation
        (Gap.noPositiveSubgapMode core)
  }

record DirectSelectedPhysicalSpectrumInputs
    {Measure TestObservable SpectralObservable Hamiltonian : Set}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    {base : R318.UnlocalizedT5StateFamilyJPresentation dataSet extension}
    {tests : R278.SelectedConnectedCovarianceTests dataSet}
    {spectrumSource : R281.ContinuumCovarianceSpectrumData
      {SpectralObservable = SpectralObservable} {Energy = ℚ}
      dataSet extension tests} : Set₂ where
  field
    directSelectedUpper : R387.DirectSelectedSpectralUpper base tests spectrumSource
    selectedLimitClosure : R342.SelectedLimitUpperClosure {dataSet = dataSet}
    positiveCandidateGap :
      Gap.PositiveEnergy
        (R281.asReconstructedClusteringSpectrum spectrumSource)
        (Gap.gapCandidate (R281.asReconstructedClusteringSpectrum spectrumSource))

    physicalSpectrum :
      PhysicalSpectrumInterpretation {Hamiltonian = Hamiltonian}
        (R281.asReconstructedClusteringSpectrum spectrumSource)

open DirectSelectedPhysicalSpectrumInputs public

directSelectedUpperBuildsPhysicalMassGapCertificate :
  ∀ {Measure TestObservable SpectralObservable Hamiltonian}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    {base : R318.UnlocalizedT5StateFamilyJPresentation dataSet extension}
    {tests : R278.SelectedConnectedCovarianceTests dataSet}
    {spectrumSource : R281.ContinuumCovarianceSpectrumData
      {SpectralObservable = SpectralObservable} {Energy = ℚ}
      dataSet extension tests} →
  DirectSelectedPhysicalSpectrumInputs
    {Hamiltonian = Hamiltonian} {spectrumSource = spectrumSource} →
  OSGap.PhysicalMassGapCertificate Hamiltonian ℚ
directSelectedUpperBuildsPhysicalMassGapCertificate inputs =
  physicalMassGapCertificateFromTransferGapCore
    (physicalSpectrum inputs)
    (Final.directSelectedUpperBuildsPositiveTransferGapCore
      (directSelectedUpper inputs)
      (selectedLimitClosure inputs)
      (positiveCandidateGap inputs))

data PhysicalSpectrumCompilerPresent : Set where
  physicalSpectrumCompilerPresent : PhysicalSpectrumCompilerPresent

r387PhysicalSpectrumCompilerLevel : ProofLevel
r387PhysicalSpectrumCompilerLevel = machineChecked

-- This is the physical same-object content corresponding to Lean's
-- `SpectralRepresentation`; it is not manufactured by the source upper.
literalPhysicalSpectrumInterpretationLevel : ProofLevel
literalPhysicalSpectrumInterpretationLevel = conditional
