{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCyclicContinuumCovarianceSpectrumRound287Exact where

------------------------------------------------------------------------
-- ROUND287 / CONTINUUM COVARIANCE + OS CYCLICITY -> SAME SPECTRUM
--
-- R281 already removes the post-hoc identity between continuum expectation
-- covariance and reconstructed `connectedCorrelation` by defining the latter on
-- the exact covariance carrier.
--
-- The older OS cyclicity owner separately proves that once every physical
-- nonzero subgap vector is meaningfully reconstructed, positive-time cyclicity
-- chooses an observable that overlaps it.  Therefore mode-observable choice and
-- the overlap witness are compiler consequences, not additional mass-gap
-- theorem leaves.
--
-- This owner composes those two reductions.  It deliberately leaves the two
-- genuine spectral inputs explicit:
--   * the spectral lower envelope produced from the actual overlap;
--   * the slow-subgap-versus-fast-clustering rate contradiction.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram
import DASHI.Physics.YangMills.BalabanConnectedCovarianceExpectationLimitRound278Exact as R278
import DASHI.Physics.YangMills.BalabanContinuumCovarianceSpectrumConstructorRound281Exact as R281
import DASHI.Physics.YangMills.BalabanClayT5OSReconstructionCyclicityExact as Cyclic
import DASHI.Physics.YangMills.BalabanClayT5ClusteringToTransferGapExact as Gap

record CyclicContinuumCovarianceSpectrumData
    {Measure TestObservable Scalar Energy Vector : Set}
    (dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable Scalar)
    (extension : R278.ScalarCovarianceConvergenceExtension dataSet)
    (tests : R278.SelectedConnectedCovarianceTests dataSet)
    : Set₁ where
  field
    cyclicity : Cyclic.PositiveTimeVacuumCyclicity TestObservable Vector
    subgapVectors : Cyclic.ReconstructedSubgapVectors Energy Vector
    subgapMeaning : Cyclic.CyclicSubgapVectorMeaning cyclicity subgapVectors

    -- The selected covariance pair used for each positive-time observable/time.
    indexFor : TestObservable → Nat → R278.Index tests

    zeroEnergy gapCandidate : Energy
    PositiveEnergy : Energy → Set
    StrictlyBelow : Energy → Energy → Set

    clusteringEnvelope : TestObservable → Nat → Scalar
    subgapSpectralEnvelope : Energy → TestObservable → Nat → Scalar
    LessEqual : Scalar → Scalar → Set

    -- Physical OS spectral theorem: a nonzero overlap gives a lower spectral
    -- contribution in the exact continuum covariance carrier.
    spectralRepresentationLowerBoundFromOverlap :
      ∀ energy (mode : Cyclic.SubgapMode subgapVectors energy) time →
      Cyclic.Overlap cyclicity
        (Cyclic.vectorOfObservable cyclicity
          (Cyclic.modeObservableFromCyclicity subgapMeaning energy mode))
        (Cyclic.modeVector subgapVectors energy mode) →
      LessEqual
        (subgapSpectralEnvelope energy
          (Cyclic.modeObservableFromCyclicity subgapMeaning energy mode) time)
        (R278.connectedCovarianceMagnitude extension
          (Gram.continuumMeasure dataSet)
          (R278.left tests
            (indexFor
              (Cyclic.modeObservableFromCyclicity subgapMeaning energy mode) time))
          (R278.right tests
            (indexFor
              (Cyclic.modeObservableFromCyclicity subgapMeaning energy mode) time)))

    -- Physical spectral/rate theorem.  The compiler does not manufacture the
    -- distinction between a slower positive subgap mode and the selected fast
    -- clustering envelope.
    slowSubgapEnvelopeContradictsFastClustering :
      ∀ energy (mode : Cyclic.SubgapMode subgapVectors energy) →
      PositiveEnergy energy → StrictlyBelow energy gapCandidate →
      (∀ time →
        LessEqual
          (subgapSpectralEnvelope energy
            (Cyclic.modeObservableFromCyclicity subgapMeaning energy mode) time)
          (R278.connectedCovarianceMagnitude extension
            (Gram.continuumMeasure dataSet)
            (R278.left tests
              (indexFor
                (Cyclic.modeObservableFromCyclicity subgapMeaning energy mode) time))
            (R278.right tests
              (indexFor
                (Cyclic.modeObservableFromCyclicity subgapMeaning energy mode) time)))) →
      (∀ time →
        LessEqual
          (R278.connectedCovarianceMagnitude extension
            (Gram.continuumMeasure dataSet)
            (R278.left tests
              (indexFor
                (Cyclic.modeObservableFromCyclicity subgapMeaning energy mode) time))
            (R278.right tests
              (indexFor
                (Cyclic.modeObservableFromCyclicity subgapMeaning energy mode) time)))
          (clusteringEnvelope
            (Cyclic.modeObservableFromCyclicity subgapMeaning energy mode) time)) →
      Gap.Empty

open CyclicContinuumCovarianceSpectrumData public

asContinuumCovarianceSpectrumData :
  ∀ {Measure TestObservable Scalar Energy Vector}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable Scalar}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    {tests : R278.SelectedConnectedCovarianceTests dataSet} →
  CyclicContinuumCovarianceSpectrumData dataSet extension tests →
  R281.ContinuumCovarianceSpectrumData
    {SpectralObservable = TestObservable} {Energy = Energy}
    dataSet extension tests
asContinuumCovarianceSpectrumData source = record
  { R281.ContinuumCovarianceSpectrumData.indexFor = indexFor source
  ; R281.ContinuumCovarianceSpectrumData.zeroEnergy = zeroEnergy source
  ; R281.ContinuumCovarianceSpectrumData.gapCandidate = gapCandidate source
  ; R281.ContinuumCovarianceSpectrumData.PositiveEnergy = PositiveEnergy source
  ; R281.ContinuumCovarianceSpectrumData.StrictlyBelow = StrictlyBelow source
  ; R281.ContinuumCovarianceSpectrumData.clusteringEnvelope = clusteringEnvelope source
  ; R281.ContinuumCovarianceSpectrumData.subgapSpectralEnvelope =
      subgapSpectralEnvelope source
  ; R281.ContinuumCovarianceSpectrumData.LessEqual = LessEqual source
  ; R281.ContinuumCovarianceSpectrumData.SubgapMode =
      Cyclic.SubgapMode (subgapVectors source)
  ; R281.ContinuumCovarianceSpectrumData.modeObservable =
      Cyclic.modeObservableFromCyclicity (subgapMeaning source)
  ; R281.ContinuumCovarianceSpectrumData.spectralRepresentationLowerBound =
      λ energy mode time →
        spectralRepresentationLowerBoundFromOverlap source energy mode time
          (Cyclic.modeObservableOverlapsSubgapVector
            (subgapMeaning source) energy mode)
  ; R281.ContinuumCovarianceSpectrumData.slowSubgapEnvelopeContradictsFastClustering =
      slowSubgapEnvelopeContradictsFastClustering source
  }

asReconstructedClusteringSpectrum :
  ∀ {Measure TestObservable Scalar Energy Vector}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable Scalar}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    {tests : R278.SelectedConnectedCovarianceTests dataSet} →
  CyclicContinuumCovarianceSpectrumData dataSet extension tests →
  Gap.ReconstructedClusteringSpectrum TestObservable Energy Scalar
asReconstructedClusteringSpectrum source =
  R281.asReconstructedClusteringSpectrum
    (asContinuumCovarianceSpectrumData source)

modeObservableChosenByCyclicity :
  ∀ {Measure TestObservable Scalar Energy Vector}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable Scalar}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    {tests : R278.SelectedConnectedCovarianceTests dataSet}
    (source : CyclicContinuumCovarianceSpectrumData dataSet extension tests)
    energy (mode : Cyclic.SubgapMode (subgapVectors source) energy) →
  Gap.modeObservable (asReconstructedClusteringSpectrum source) energy mode
  ≡ Cyclic.modeObservableFromCyclicity (subgapMeaning source) energy mode
modeObservableChosenByCyclicity source energy mode = refl

continuumCovarianceIsCyclicSpectrumCorrelation :
  ∀ {Measure TestObservable Scalar Energy Vector}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable Scalar}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    {tests : R278.SelectedConnectedCovarianceTests dataSet}
    (source : CyclicContinuumCovarianceSpectrumData dataSet extension tests)
    observable time →
  R278.connectedCovarianceMagnitude extension
    (Gram.continuumMeasure dataSet)
    (R278.left tests (indexFor source observable time))
    (R278.right tests (indexFor source observable time))
  ≡ Gap.connectedCorrelation
      (asReconstructedClusteringSpectrum source) observable time
continuumCovarianceIsCyclicSpectrumCorrelation source observable time = refl

record Round287Boundary : Set where
  constructor round287-boundary
  field
    postHocCovarianceSpectrumIdentityRequired : Bool
    postHocCovarianceSpectrumIdentityRequiredIsFalse :
      postHocCovarianceSpectrumIdentityRequired ≡ false

    subgapObservableChoicePrimitive : Bool
    subgapObservableChoicePrimitiveIsFalse :
      subgapObservableChoicePrimitive ≡ false

    subgapOverlapAfterCyclicityPrimitive : Bool
    subgapOverlapAfterCyclicityPrimitiveIsFalse :
      subgapOverlapAfterCyclicityPrimitive ≡ false

    physicalCyclicityAndNonzeroMeaningStillRequired : Bool
    physicalCyclicityAndNonzeroMeaningStillRequiredIsTrue :
      physicalCyclicityAndNonzeroMeaningStillRequired ≡ true

    spectralLowerBoundFromOverlapStillPhysical : Bool
    spectralLowerBoundFromOverlapStillPhysicalIsTrue :
      spectralLowerBoundFromOverlapStillPhysical ≡ true

    slowVersusFastRateTheoremStillPhysical : Bool
    slowVersusFastRateTheoremStillPhysicalIsTrue :
      slowVersusFastRateTheoremStillPhysical ≡ true

canonicalRound287Boundary : Round287Boundary
canonicalRound287Boundary =
  round287-boundary false refl false refl false refl true refl true refl true refl

round287CyclicCovarianceSpectrumCompilerLevel : ProofLevel
round287CyclicCovarianceSpectrumCompilerLevel = machineChecked

round287PhysicalPositiveTimeCyclicityLevel : ProofLevel
round287PhysicalPositiveTimeCyclicityLevel = Cyclic.physicalPositiveTimeCylinderCyclicityInputsLevel

round287PhysicalSubgapNonzeroMeaningLevel : ProofLevel
round287PhysicalSubgapNonzeroMeaningLevel = Cyclic.physicalSubgapVectorNonzeroMeaningInputsLevel

round287PhysicalSpectralLowerBoundFromOverlapLevel : ProofLevel
round287PhysicalSpectralLowerBoundFromOverlapLevel =
  Cyclic.physicalSpectralLowerBoundFromOverlapInputsLevel

round287SlowVersusFastRateTheoremLevel : ProofLevel
round287SlowVersusFastRateTheoremLevel = conditional
