{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanSubgapSeparatingTimeRound288Exact where

------------------------------------------------------------------------
-- ROUND288 / PRE-RATE SPECTRAL CORE + ONE SEPARATING TIME
--
-- Do not ask for the historical all-time slow-vs-fast contradiction as a
-- primitive field.  Build the spectrum in two stages:
--   1. continuum covariance + OS cyclicity + spectral lower representation;
--   2. for every alleged positive subgap mode, one time where its lower
--      envelope and the clustering upper cannot coexist.
-- The historical contradiction field is compiler output from stage 2.
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

record CyclicCovarianceSpectralCore
    {Measure TestObservable Scalar Energy Vector : Set}
    (dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable Scalar)
    (extension : R278.ScalarCovarianceConvergenceExtension dataSet)
    (tests : R278.SelectedConnectedCovarianceTests dataSet) : Set₁ where
  field
    cyclicity : Cyclic.PositiveTimeVacuumCyclicity TestObservable Vector
    subgapVectors : Cyclic.ReconstructedSubgapVectors Energy Vector
    subgapMeaning : Cyclic.CyclicSubgapVectorMeaning cyclicity subgapVectors
    indexFor : TestObservable → Nat → R278.Index tests

    zeroEnergy gapCandidate : Energy
    PositiveEnergy : Energy → Set
    StrictlyBelow : Energy → Energy → Set
    clusteringEnvelope : TestObservable → Nat → Scalar
    subgapSpectralEnvelope : Energy → TestObservable → Nat → Scalar
    LessEqual : Scalar → Scalar → Set

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

open CyclicCovarianceSpectralCore public

record SubgapSeparatingTimeData
    {Measure TestObservable Scalar Energy Vector : Set}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable Scalar}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    {tests : R278.SelectedConnectedCovarianceTests dataSet}
    (core : CyclicCovarianceSpectralCore dataSet extension tests) : Set₁ where
  field
    separatingTime :
      ∀ energy (mode : Cyclic.SubgapMode (subgapVectors core) energy) →
      PositiveEnergy core energy →
      StrictlyBelow core energy (gapCandidate core) → Nat

    lowerAndUpperContradictAtSeparatingTime :
      ∀ energy (mode : Cyclic.SubgapMode (subgapVectors core) energy)
        (positive : PositiveEnergy core energy)
        (below : StrictlyBelow core energy (gapCandidate core)) →
      let time = separatingTime energy mode positive below
          observable =
            Cyclic.modeObservableFromCyclicity (subgapMeaning core) energy mode
          correlation =
            R278.connectedCovarianceMagnitude extension
              (Gram.continuumMeasure dataSet)
              (R278.left tests (indexFor core observable time))
              (R278.right tests (indexFor core observable time))
      in
      LessEqual core
        (subgapSpectralEnvelope core energy observable time) correlation →
      LessEqual core correlation
        (clusteringEnvelope core observable time) →
      Gap.Empty

open SubgapSeparatingTimeData public

slowFastContradiction :
  ∀ {Measure TestObservable Scalar Energy Vector}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable Scalar}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    {tests : R278.SelectedConnectedCovarianceTests dataSet}
    {core : CyclicCovarianceSpectralCore dataSet extension tests} →
  SubgapSeparatingTimeData core →
  ∀ energy (mode : Cyclic.SubgapMode (subgapVectors core) energy) →
  PositiveEnergy core energy →
  StrictlyBelow core energy (gapCandidate core) →
  (∀ time →
    LessEqual core
      (subgapSpectralEnvelope core energy
        (Cyclic.modeObservableFromCyclicity (subgapMeaning core) energy mode) time)
      (R278.connectedCovarianceMagnitude extension
        (Gram.continuumMeasure dataSet)
        (R278.left tests
          (indexFor core
            (Cyclic.modeObservableFromCyclicity (subgapMeaning core) energy mode) time))
        (R278.right tests
          (indexFor core
            (Cyclic.modeObservableFromCyclicity (subgapMeaning core) energy mode) time)))) →
  (∀ time →
    LessEqual core
      (R278.connectedCovarianceMagnitude extension
        (Gram.continuumMeasure dataSet)
        (R278.left tests
          (indexFor core
            (Cyclic.modeObservableFromCyclicity (subgapMeaning core) energy mode) time))
        (R278.right tests
          (indexFor core
            (Cyclic.modeObservableFromCyclicity (subgapMeaning core) energy mode) time)))
      (clusteringEnvelope core
        (Cyclic.modeObservableFromCyclicity (subgapMeaning core) energy mode) time)) →
  Gap.Empty
slowFastContradiction separation energy mode positive below lower upper =
  lowerAndUpperContradictAtSeparatingTime separation energy mode positive below
    (lower (separatingTime separation energy mode positive below))
    (upper (separatingTime separation energy mode positive below))

asContinuumCovarianceSpectrumData :
  ∀ {Measure TestObservable Scalar Energy Vector}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable Scalar}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    {tests : R278.SelectedConnectedCovarianceTests dataSet}
    (core : CyclicCovarianceSpectralCore dataSet extension tests) →
  SubgapSeparatingTimeData core →
  R281.ContinuumCovarianceSpectrumData
    {SpectralObservable = TestObservable} {Energy = Energy}
    dataSet extension tests
asContinuumCovarianceSpectrumData core separation = record
  { R281.ContinuumCovarianceSpectrumData.indexFor = indexFor core
  ; R281.ContinuumCovarianceSpectrumData.zeroEnergy = zeroEnergy core
  ; R281.ContinuumCovarianceSpectrumData.gapCandidate = gapCandidate core
  ; R281.ContinuumCovarianceSpectrumData.PositiveEnergy = PositiveEnergy core
  ; R281.ContinuumCovarianceSpectrumData.StrictlyBelow = StrictlyBelow core
  ; R281.ContinuumCovarianceSpectrumData.clusteringEnvelope = clusteringEnvelope core
  ; R281.ContinuumCovarianceSpectrumData.subgapSpectralEnvelope =
      subgapSpectralEnvelope core
  ; R281.ContinuumCovarianceSpectrumData.LessEqual = LessEqual core
  ; R281.ContinuumCovarianceSpectrumData.SubgapMode =
      Cyclic.SubgapMode (subgapVectors core)
  ; R281.ContinuumCovarianceSpectrumData.modeObservable =
      Cyclic.modeObservableFromCyclicity (subgapMeaning core)
  ; R281.ContinuumCovarianceSpectrumData.spectralRepresentationLowerBound =
      λ energy mode time →
        spectralRepresentationLowerBoundFromOverlap core energy mode time
          (Cyclic.modeObservableOverlapsSubgapVector
            (subgapMeaning core) energy mode)
  ; R281.ContinuumCovarianceSpectrumData.slowSubgapEnvelopeContradictsFastClustering =
      slowFastContradiction separation
  }

record Round288Boundary : Set where
  constructor round288-boundary
  field
    fullSlowFastImplicationPrimitive : Bool
    fullSlowFastImplicationPrimitiveIsFalse :
      fullSlowFastImplicationPrimitive ≡ false
    oneSeparatingTimePerSubgapModeSuffices : Bool
    oneSeparatingTimePerSubgapModeSufficesIsTrue :
      oneSeparatingTimePerSubgapModeSuffices ≡ true
    modeObservableAndOverlapCompilerOwned : Bool
    modeObservableAndOverlapCompilerOwnedIsTrue :
      modeObservableAndOverlapCompilerOwned ≡ true
    separatingTimeConstructionStillPhysical : Bool
    separatingTimeConstructionStillPhysicalIsTrue :
      separatingTimeConstructionStillPhysical ≡ true

canonicalRound288Boundary : Round288Boundary
canonicalRound288Boundary =
  round288-boundary false refl true refl true refl true refl

round288PreRateSpectrumCompilerLevel : ProofLevel
round288PreRateSpectrumCompilerLevel = machineChecked

round288PhysicalSpectralLowerBoundFromOverlapLevel : ProofLevel
round288PhysicalSpectralLowerBoundFromOverlapLevel =
  Cyclic.physicalSpectralLowerBoundFromOverlapInputsLevel

round288PhysicalSeparatingTimeLevel : ProofLevel
round288PhysicalSeparatingTimeLevel = conditional
