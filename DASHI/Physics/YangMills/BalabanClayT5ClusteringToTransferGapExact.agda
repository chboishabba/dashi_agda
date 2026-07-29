module DASHI.Physics.YangMills.BalabanClayT5ClusteringToTransferGapExact where

open import Agda.Builtin.Nat using (Nat)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanClayT5LimitAndNontrivialityExact as Limit

------------------------------------------------------------------------
-- Primary provenance.
--
-- Konrad Osterwalder and Robert Schrader,
-- "Axioms for Euclidean Green's Functions",
-- Communications in Mathematical Physics 31 (1973), 83--112.
-- DOI: 10.1007/BF01645738.
--
-- Konrad Osterwalder and Robert Schrader,
-- "Axioms for Euclidean Green's Functions II",
-- Communications in Mathematical Physics 42 (1975), 281--305.
-- DOI: 10.1007/BF01608978.
--
-- O. Penrose and J. L. Lebowitz,
-- "On the Exponential Decay of Correlation Functions",
-- Communications in Mathematical Physics 39 (1974), 165--184.
-- DOI: 10.1007/BF01614239.
--
-- The OS papers own reconstruction of the positive transfer semigroup.  The
-- finite contradiction below isolates the remaining spectral content: a mode
-- strictly below the proposed gap gives a slower positive spectral contribution,
-- while OS4 supplies a faster uniform upper envelope.  Density/overlap and the
-- spectral lower representation are not silently inferred from the word
-- "clustered".
------------------------------------------------------------------------

data Empty : Set where

record ReconstructedClusteringSpectrum
    (Observable Energy Bound : Set) : Set₁ where
  field
    zeroEnergy gapCandidate : Energy
    PositiveEnergy : Energy → Set
    StrictlyBelow : Energy → Energy → Set

    connectedCorrelation : Observable → Nat → Bound
    clusteringEnvelope : Observable → Nat → Bound
    subgapSpectralEnvelope : Energy → Observable → Nat → Bound
    LessEqual : Bound → Bound → Set

    clusteringUpperBound : ∀ observable time →
      LessEqual
        (connectedCorrelation observable time)
        (clusteringEnvelope observable time)

    SubgapMode : Energy → Set
    modeObservable : ∀ energy → SubgapMode energy → Observable

    spectralRepresentationLowerBound : ∀ energy mode time →
      LessEqual
        (subgapSpectralEnvelope energy (modeObservable energy mode) time)
        (connectedCorrelation (modeObservable energy mode) time)

    slowSubgapEnvelopeContradictsFastClustering : ∀ energy mode →
      PositiveEnergy energy → StrictlyBelow energy gapCandidate →
      (∀ time →
        LessEqual
          (subgapSpectralEnvelope energy (modeObservable energy mode) time)
          (connectedCorrelation (modeObservable energy mode) time)) →
      (∀ time →
        LessEqual
          (connectedCorrelation (modeObservable energy mode) time)
          (clusteringEnvelope (modeObservable energy mode) time)) →
      Empty

open ReconstructedClusteringSpectrum public

NoPositiveSubgapMode :
  ∀ {Observable Energy Bound} →
  ReconstructedClusteringSpectrum Observable Energy Bound → Set
NoPositiveSubgapMode dataSet = ∀ energy →
  PositiveEnergy dataSet energy →
  StrictlyBelow dataSet energy (gapCandidate dataSet) →
  SubgapMode dataSet energy → Empty

exponentialClusteringExcludesPositiveSubgapMode :
  ∀ {Observable Energy Bound}
    (dataSet : ReconstructedClusteringSpectrum Observable Energy Bound) →
  NoPositiveSubgapMode dataSet
exponentialClusteringExcludesPositiveSubgapMode dataSet
  energy positive below mode =
  slowSubgapEnvelopeContradictsFastClustering dataSet
    energy mode positive below
    (spectralRepresentationLowerBound dataSet energy mode)
    (clusteringUpperBound dataSet (modeObservable dataSet energy mode))

record PositiveTransferGap
    {Observable Energy Bound : Set}
    (dataSet : ReconstructedClusteringSpectrum Observable Energy Bound) : Set₁ where
  field
    gapCandidatePositive : PositiveEnergy dataSet (gapCandidate dataSet)
    noPositiveSubgapMode : NoPositiveSubgapMode dataSet

open PositiveTransferGap public

positiveTransferGapFromClusteringCutset :
  ∀ {Observable Energy Bound}
    (dataSet : ReconstructedClusteringSpectrum Observable Energy Bound) →
  PositiveEnergy dataSet (gapCandidate dataSet) →
  PositiveTransferGap dataSet
positiveTransferGapFromClusteringCutset dataSet positiveGap = record
  { PositiveTransferGap.gapCandidatePositive = positiveGap
  ; PositiveTransferGap.noPositiveSubgapMode =
      exponentialClusteringExcludesPositiveSubgapMode dataSet
  }

record OS4SpectralInterpretation
    {Measure Schwinger Observable Energy Bound : Set}
    (closure : Limit.FiniteToContinuumOSClosure Measure Schwinger)
    (spectrum : ReconstructedClusteringSpectrum Observable Energy Bound) : Set₁ where
  field
    closureClusteringMeaning :
      Limit.Clustered closure
        (Limit.schwinger closure (Limit.continuumMeasure closure)) →
      ∀ observable time →
      LessEqual spectrum
        (connectedCorrelation spectrum observable time)
        (clusteringEnvelope spectrum observable time)

    candidateGapPositive : PositiveEnergy spectrum (gapCandidate spectrum)

open OS4SpectralInterpretation public

positiveTransferGapFromOS4 :
  ∀ {Measure Schwinger Observable Energy Bound}
    {closure : Limit.FiniteToContinuumOSClosure Measure Schwinger}
    {spectrum : ReconstructedClusteringSpectrum Observable Energy Bound} →
  OS4SpectralInterpretation closure spectrum →
  Limit.Clustered closure
    (Limit.schwinger closure (Limit.continuumMeasure closure)) →
  PositiveTransferGap spectrum
positiveTransferGapFromOS4 {spectrum = spectrum} interpretation clustered =
  positiveTransferGapFromClusteringCutset spectrum
    (candidateGapPositive interpretation)

clusteringSpectralContradictionAssemblyLevel : ProofLevel
clusteringSpectralContradictionAssemblyLevel = machineChecked

positiveTransferGapAssemblyLevel : ProofLevel
positiveTransferGapAssemblyLevel = machineChecked

os4ToTransferGapAssemblyLevel : ProofLevel
os4ToTransferGapAssemblyLevel = machineChecked

physicalSpectralRepresentationLowerBoundInputsLevel : ProofLevel
physicalSpectralRepresentationLowerBoundInputsLevel = conditional

physicalObservableSubgapOverlapInputsLevel : ProofLevel
physicalObservableSubgapOverlapInputsLevel = conditional

physicalSlowVersusFastRateComparisonInputsLevel : ProofLevel
physicalSlowVersusFastRateComparisonInputsLevel = conditional

physicalOS4ClusteringMeaningInputsLevel : ProofLevel
physicalOS4ClusteringMeaningInputsLevel = conditional
