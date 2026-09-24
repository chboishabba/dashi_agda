module DASHI.Physics.YangMills.YMClayR387CanonicalEndgameExact where

------------------------------------------------------------------------
-- R387 -> PHYSICAL SPECTRUM -> ROUND308 -> RECOVERY -> MASS GAP CONCLUSION
--
-- This is the preferred source-side endgame after #987.  It removes the
-- generic `CommonContinuumOSRoute` from the active path.  The direct selected
-- source upper constructs PositiveTransferGapCore; a physical spectral
-- interpretation turns that core into the existing PhysicalMassGapCertificate;
-- the certificate is inserted into the existing Round308 same-Hamiltonian
-- consumer; and the canonical vacuum-orthogonal recovery compiler supplies the
-- continuum form-gap component of the final parity conclusion.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
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
import DASHI.Physics.YangMills.BalabanVacuumOrthogonalMoscoRecoveryExact as Recovery
import DASHI.Physics.YangMills.YMKatoClosedFormHamiltonianExact as Kato
import DASHI.Physics.YangMills.BalabanClayDirectTerminalConsumerCutRound308Exact as R308
import DASHI.Physics.YangMills.YMClayMassGapAssemblyParityExact as Assembly
import DASHI.Physics.YangMills.YMClayR387PhysicalSpectrumExact as Spectrum
import DASHI.Physics.YangMills.YMClayCanonicalContinuumOSWeldExact as Canonical

record R387CanonicalPhysicalEndgameInputs
    {Measure TestObservable SpectralObservable : Set}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    {base : R318.UnlocalizedT5StateFamilyJPresentation dataSet extension}
    {tests : R278.SelectedConnectedCovarianceTests dataSet}
    {spectrumSource : R281.ContinuumCovarianceSpectrumData
      {SpectralObservable = SpectralObservable} {Energy = ℚ}
      dataSet extension tests}
    (Hilbert Scalar Hamiltonian Vacuum ContinuumTheory : Set) : Set₂ where
  field
    directSelectedUpper : R387.DirectSelectedSpectralUpper base tests spectrumSource
    selectedLimitClosure : R342.SelectedLimitUpperClosure {dataSet = dataSet}
    positiveCandidateGap :
      Gap.PositiveEnergy
        (R281.asReconstructedClusteringSpectrum spectrumSource)
        (Gap.gapCandidate (R281.asReconstructedClusteringSpectrum spectrumSource))

    physicalSpectrum :
      Spectrum.PhysicalSpectrumInterpretation {Hamiltonian = Hamiltonian}
        (R281.asReconstructedClusteringSpectrum spectrumSource)

    recoverySystem : Recovery.VacuumOrthogonalRecoverySystem

    continuumTheory : ContinuumTheory
    PhysicalYangMillsContinuumTheory : ContinuumTheory → Set
    physicalContinuumTheory : PhysicalYangMillsContinuumTheory continuumTheory
    NontrivialContinuumTheory : ContinuumTheory → Set
    continuumNontrivial : NontrivialContinuumTheory continuumTheory

    physicalKatoPackage : Kato.KatoM7OperatorPackage Hilbert Scalar

    PhysicalHamiltonianMeaning : Hamiltonian → Set
    reconstructedGapHamiltonianIsPhysicalYM :
      PhysicalHamiltonianMeaning (Spectrum.physicalHamiltonian physicalSpectrum)

    KatoHamiltonianMeaning :
      Kato.AssociatedSelfAdjointOperator
        (Kato.physicalForm (Kato.physical physicalKatoPackage)) → Set
    katoAssociatedHamiltonianIsPhysicalYM :
      KatoHamiltonianMeaning (Kato.hamiltonian physicalKatoPackage)

    SameHamiltonianDynamics :
      Hamiltonian →
      Kato.AssociatedSelfAdjointOperator
        (Kato.physicalForm (Kato.physical physicalKatoPackage)) → Set
    sameHamiltonianDynamics :
      SameHamiltonianDynamics
        (Spectrum.physicalHamiltonian physicalSpectrum)
        (Kato.hamiltonian physicalKatoPackage)

    vacuum : Vacuum

    sameGap :
      Gap.gapCandidate (R281.asReconstructedClusteringSpectrum spectrumSource)
      ≡ Recovery.gapConstant recoverySystem

    VacuumSectorResolvent : Set
    vacuumSectorResolvent : VacuumSectorResolvent

open R387CanonicalPhysicalEndgameInputs public

sourceTransferGapCore :
  ∀ {Measure TestObservable SpectralObservable
      Hilbert Scalar Hamiltonian Vacuum ContinuumTheory}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    {base : R318.UnlocalizedT5StateFamilyJPresentation dataSet extension}
    {tests : R278.SelectedConnectedCovarianceTests dataSet}
    {spectrumSource : R281.ContinuumCovarianceSpectrumData
      {SpectralObservable = SpectralObservable} {Energy = ℚ}
      dataSet extension tests} →
  (inputs : R387CanonicalPhysicalEndgameInputs
    {spectrumSource = spectrumSource}
    Hilbert Scalar Hamiltonian Vacuum ContinuumTheory) →
  Gap.PositiveTransferGapCore
    (R281.asReconstructedClusteringSpectrum spectrumSource)
sourceTransferGapCore inputs =
  Final.directSelectedUpperBuildsPositiveTransferGapCore
    (directSelectedUpper inputs)
    (selectedLimitClosure inputs)
    (positiveCandidateGap inputs)

sourcePhysicalMassGapCertificate :
  ∀ {Measure TestObservable SpectralObservable
      Hilbert Scalar Hamiltonian Vacuum ContinuumTheory}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    {base : R318.UnlocalizedT5StateFamilyJPresentation dataSet extension}
    {tests : R278.SelectedConnectedCovarianceTests dataSet}
    {spectrumSource : R281.ContinuumCovarianceSpectrumData
      {SpectralObservable = SpectralObservable} {Energy = ℚ}
      dataSet extension tests} →
  (inputs : R387CanonicalPhysicalEndgameInputs
    {spectrumSource = spectrumSource}
    Hilbert Scalar Hamiltonian Vacuum ContinuumTheory) →
  OSGap.PhysicalMassGapCertificate Hamiltonian ℚ
sourcePhysicalMassGapCertificate inputs =
  Spectrum.physicalMassGapCertificateFromTransferGapCore
    (physicalSpectrum inputs)
    (sourceTransferGapCore inputs)

asRound308Terminal :
  ∀ {Measure TestObservable SpectralObservable
      Hilbert Scalar Hamiltonian Vacuum ContinuumTheory}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    {base : R318.UnlocalizedT5StateFamilyJPresentation dataSet extension}
    {tests : R278.SelectedConnectedCovarianceTests dataSet}
    {spectrumSource : R281.ContinuumCovarianceSpectrumData
      {SpectralObservable = SpectralObservable} {Energy = ℚ}
      dataSet extension tests} →
  (inputs : R387CanonicalPhysicalEndgameInputs
    {spectrumSource = spectrumSource}
    Hilbert Scalar Hamiltonian Vacuum ContinuumTheory) →
  R308.DirectTerminalClayConsumers Hilbert Scalar Hamiltonian ℚ ContinuumTheory
asRound308Terminal inputs = record
  { R308.DirectTerminalClayConsumers.continuumTheory = continuumTheory inputs
  ; R308.DirectTerminalClayConsumers.PhysicalYangMillsContinuumTheory =
      PhysicalYangMillsContinuumTheory inputs
  ; R308.DirectTerminalClayConsumers.physicalContinuumTheory =
      physicalContinuumTheory inputs
  ; R308.DirectTerminalClayConsumers.NontrivialContinuumTheory =
      NontrivialContinuumTheory inputs
  ; R308.DirectTerminalClayConsumers.continuumNontrivial =
      continuumNontrivial inputs
  ; R308.DirectTerminalClayConsumers.physicalKatoPackage =
      physicalKatoPackage inputs
  ; R308.DirectTerminalClayConsumers.massGap =
      sourcePhysicalMassGapCertificate inputs
  ; R308.DirectTerminalClayConsumers.PhysicalHamiltonianMeaning =
      PhysicalHamiltonianMeaning inputs
  ; R308.DirectTerminalClayConsumers.reconstructedGapHamiltonianIsPhysicalYM =
      reconstructedGapHamiltonianIsPhysicalYM inputs
  ; R308.DirectTerminalClayConsumers.KatoHamiltonianMeaning =
      KatoHamiltonianMeaning inputs
  ; R308.DirectTerminalClayConsumers.katoAssociatedHamiltonianIsPhysicalYM =
      katoAssociatedHamiltonianIsPhysicalYM inputs
  ; R308.DirectTerminalClayConsumers.SameHamiltonianDynamics =
      SameHamiltonianDynamics inputs
  ; R308.DirectTerminalClayConsumers.sameHamiltonianDynamics =
      sameHamiltonianDynamics inputs
  }

asCanonicalPhysicalEndgame :
  ∀ {Measure TestObservable SpectralObservable
      Hilbert Scalar Hamiltonian Vacuum ContinuumTheory}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    {base : R318.UnlocalizedT5StateFamilyJPresentation dataSet extension}
    {tests : R278.SelectedConnectedCovarianceTests dataSet}
    {spectrumSource : R281.ContinuumCovarianceSpectrumData
      {SpectralObservable = SpectralObservable} {Energy = ℚ}
      dataSet extension tests} →
  (inputs : R387CanonicalPhysicalEndgameInputs
    {spectrumSource = spectrumSource}
    Hilbert Scalar Hamiltonian Vacuum ContinuumTheory) →
  Canonical.CanonicalPhysicalMassGapEndgame
    Hilbert Scalar Hamiltonian Vacuum ContinuumTheory
asCanonicalPhysicalEndgame inputs = record
  { Canonical.CanonicalPhysicalMassGapEndgame.recoverySystem = recoverySystem inputs
  ; Canonical.CanonicalPhysicalMassGapEndgame.terminal = asRound308Terminal inputs
  ; Canonical.CanonicalPhysicalMassGapEndgame.vacuum = vacuum inputs
  ; Canonical.CanonicalPhysicalMassGapEndgame.sameGap = sameGap inputs
  ; Canonical.CanonicalPhysicalMassGapEndgame.VacuumSectorResolvent =
      VacuumSectorResolvent inputs
  ; Canonical.CanonicalPhysicalMassGapEndgame.vacuumSectorResolvent =
      vacuumSectorResolvent inputs
  }

r387DirectSelectedSourceBuildsCanonicalMassGapConclusion :
  ∀ {Measure TestObservable SpectralObservable
      Hilbert Scalar Hamiltonian Vacuum ContinuumTheory}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    {base : R318.UnlocalizedT5StateFamilyJPresentation dataSet extension}
    {tests : R278.SelectedConnectedCovarianceTests dataSet}
    {spectrumSource : R281.ContinuumCovarianceSpectrumData
      {SpectralObservable = SpectralObservable} {Energy = ℚ}
      dataSet extension tests} →
  R387CanonicalPhysicalEndgameInputs
    {spectrumSource = spectrumSource}
    Hilbert Scalar Hamiltonian Vacuum ContinuumTheory →
  Assembly.MassGapConclusion Hamiltonian Vacuum ℚ
r387DirectSelectedSourceBuildsCanonicalMassGapConclusion inputs =
  Canonical.canonicalPhysicalMassGapConclusion
    (asCanonicalPhysicalEndgame inputs)

data CanonicalR387EndgameCompilerPresent : Set where
  canonicalR387EndgameCompilerPresent : CanonicalR387EndgameCompilerPresent

r387CanonicalEndgameCompilerLevel : ProofLevel
r387CanonicalEndgameCompilerLevel = machineChecked

-- Physical leaves intentionally remain explicit in the record above.
r387PhysicalSpectrumMeaningLevel : ProofLevel
r387PhysicalSpectrumMeaningLevel = Spectrum.literalPhysicalSpectrumInterpretationLevel

r387PhysicalRecoverySystemLevel : ProofLevel
r387PhysicalRecoverySystemLevel = Recovery.physicalVacuumRecoveryProducerLevel

r387PhysicalSameHamiltonianLevel : ProofLevel
r387PhysicalSameHamiltonianLevel = R308.round308TerminalConsumerInhabitationLevel

r387AgdaResolventCompilerLevel : ProofLevel
r387AgdaResolventCompilerLevel = Canonical.agdaVacuumSectorResolventCompilerLevel
