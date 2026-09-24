{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YMClayR387PhysicalMassGapCertificateExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
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

record R387PhysicalSpectralInterpretation
    {Observable Energy Bound Hamiltonian : Set}
    (spectrum : Gap.ReconstructedClusteringSpectrum Observable Energy Bound)
    (HamiltonianCarrier : Set) : Set₁ where
  field
    physicalHamiltonian : HamiltonianCarrier

    PhysicalSpectrumAboveSelectedGap : Set
    physicalSpectrumAboveSelectedGap : PhysicalSpectrumAboveSelectedGap

    noSubgapCoreHasPhysicalMeaning :
      Gap.NoPositiveSubgapMode spectrum →
      PhysicalSpectrumAboveSelectedGap

open R387PhysicalSpectralInterpretation public

physicalMassGapCertificateFromTransferGapCore :
  ∀ {Observable Energy Bound Hamiltonian}
    {spectrum : Gap.ReconstructedClusteringSpectrum Observable Energy Bound} →
  R387PhysicalSpectralInterpretation spectrum Hamiltonian →
  Gap.PositiveTransferGapCore spectrum →
  OSGap.PhysicalMassGapCertificate Hamiltonian Energy
physicalMassGapCertificateFromTransferGapCore {spectrum = spectrum}
    interpretation core = record
  { OSGap.PhysicalMassGapCertificate.hamiltonian =
      physicalHamiltonian interpretation
  ; OSGap.PhysicalMassGapCertificate.gap = Gap.gapCandidate spectrum
  ; OSGap.PhysicalMassGapCertificate.Positive = Gap.PositiveEnergy spectrum
  ; OSGap.PhysicalMassGapCertificate.gapPositive =
      Gap.gapCandidatePositive core
  ; OSGap.PhysicalMassGapCertificate.SpectrumAboveVacuumGap =
      PhysicalSpectrumAboveSelectedGap interpretation
  ; OSGap.PhysicalMassGapCertificate.spectrumAboveVacuumGap =
      noSubgapCoreHasPhysicalMeaning interpretation
        (Gap.noPositiveSubgapMode core)
  }

record DirectR387PhysicalMassGapInputs
    {Measure TestObservable SpectralObservable Energy Hamiltonian : Set}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    {base : R318.UnlocalizedT5StateFamilyJPresentation dataSet extension}
    {tests : R278.SelectedConnectedCovarianceTests dataSet}
    (spectrumSource : R281.ContinuumCovarianceSpectrumData
      {SpectralObservable = SpectralObservable} {Energy = Energy}
      dataSet extension tests) : Set₁ where
  field
    directSelectedUpper :
      R387.DirectSelectedSpectralUpper base tests spectrumSource

    selectedLimitClosure : R342.SelectedLimitUpperClosure {dataSet = dataSet}

    positiveCandidateGap :
      Gap.PositiveEnergy
        (R281.asReconstructedClusteringSpectrum spectrumSource)
        (Gap.gapCandidate (R281.asReconstructedClusteringSpectrum spectrumSource))

    physicalSpectralInterpretation :
      R387PhysicalSpectralInterpretation
        (R281.asReconstructedClusteringSpectrum spectrumSource)
        Hamiltonian

open DirectR387PhysicalMassGapInputs public

directR387BuildsPhysicalMassGapCertificate :
  ∀ {Measure TestObservable SpectralObservable Energy Hamiltonian}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    {base : R318.UnlocalizedT5StateFamilyJPresentation dataSet extension}
    {tests : R278.SelectedConnectedCovarianceTests dataSet}
    {spectrumSource : R281.ContinuumCovarianceSpectrumData
      {SpectralObservable = SpectralObservable} {Energy = Energy}
      dataSet extension tests} →
  DirectR387PhysicalMassGapInputs
    {Hamiltonian = Hamiltonian} spectrumSource →
  OSGap.PhysicalMassGapCertificate Hamiltonian Energy
directR387BuildsPhysicalMassGapCertificate
    {spectrumSource = spectrumSource} inputs =
  physicalMassGapCertificateFromTransferGapCore
    (physicalSpectralInterpretation inputs)
    (Final.directSelectedUpperBuildsPositiveTransferGapCore
      (directSelectedUpper inputs)
      (selectedLimitClosure inputs)
      (positiveCandidateGap inputs))

data PhysicalCertificateCompilerPresent : Set where
  physicalCertificateCompilerPresent : PhysicalCertificateCompilerPresent

physicalCertificateCompilerWitness : PhysicalCertificateCompilerPresent
physicalCertificateCompilerWitness = physicalCertificateCompilerPresent

-- Explicit source-written adapter term; no exact-head Agda kernel receipt was
-- run in this connector tranche, so the metadata remains fail-closed.
r387ToPhysicalMassGapCertificateCompilerLevel : ProofLevel
r387ToPhysicalMassGapCertificateCompilerLevel = conditional

r387PhysicalSpectrumInterpretationLevel : ProofLevel
r387PhysicalSpectrumInterpretationLevel = conditional

prebuiltPhysicalMassGapCertificateRequired : Bool
prebuiltPhysicalMassGapCertificateRequired = false

prebuiltPhysicalMassGapCertificateRequiredIsFalse :
  prebuiltPhysicalMassGapCertificateRequired ≡ false
prebuiltPhysicalMassGapCertificateRequiredIsFalse = refl
