module DASHI.Physics.YangMills.BalabanClayT5ClusteringToTransferGapExact where

open import Agda.Builtin.Nat using (Nat)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanClayT5LimitAndNontrivialityExact as Limit

------------------------------------------------------------------------
-- Primary provenance.
--
-- Konrad Osterwalder and Robert Schrader,
-- "Axioms for Euclidean Green's Functions", Communications in Mathematical
-- Physics 31 (1973), 83--112. DOI: 10.1007/BF01645738.
--
-- Konrad Osterwalder and Robert Schrader,
-- "Axioms for Euclidean Green's Functions II", Communications in Mathematical
-- Physics 42 (1975), 281--305. DOI: 10.1007/BF01608978.
--
-- O. Penrose and J. Lebowitz,
-- "On the Exponential Decay of Correlation Functions", Communications in
-- Mathematical Physics 39 (1974), 165--184. DOI: 10.1007/BF01614239.
--
-- The OS papers own reconstruction of the positive transfer semigroup.  The
-- finite contradiction below isolates the remaining spectral content: a mode
-- strictly below the proposed gap gives a slower positive spectral contribution,
-- while clustering supplies a faster upper envelope.  Density/overlap and the
-- spectral lower representation are not silently inferred from the word
-- "clustered".
--
-- R277 / NS-R503 MINIMIZATION
-- The contradiction only evaluates the clustering upper at `modeObservable` for
-- a hypothetical positive subgap mode.  A bound for EVERY observable is
-- sufficient but stronger than the spectral consumer.  The canonical primitive
-- is therefore `SubgapModeClusteringUpper`; global `ClusteringUpperBound` is
-- retained as a compatibility/stronger producer.
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

ClusteringUpperBound :
  ∀ {Observable Energy Bound} →
  ReconstructedClusteringSpectrum Observable Energy Bound → Set
ClusteringUpperBound dataSet = ∀ observable time →
  LessEqual dataSet
    (connectedCorrelation dataSet observable time)
    (clusteringEnvelope dataSet observable time)

-- R277 least-privilege spectral consumer: only observables that actually arise
-- from a hypothetical positive subgap mode need the fast upper envelope.
SubgapModeClusteringUpper :
  ∀ {Observable Energy Bound} →
  ReconstructedClusteringSpectrum Observable Energy Bound → Set
SubgapModeClusteringUpper dataSet = ∀ energy mode time →
  LessEqual dataSet
    (connectedCorrelation dataSet (modeObservable dataSet energy mode) time)
    (clusteringEnvelope dataSet (modeObservable dataSet energy mode) time)

globalClusteringUpperImpliesSubgapModeUpper :
  ∀ {Observable Energy Bound}
    (dataSet : ReconstructedClusteringSpectrum Observable Energy Bound) →
  ClusteringUpperBound dataSet →
  SubgapModeClusteringUpper dataSet
globalClusteringUpperImpliesSubgapModeUpper dataSet upper energy mode time =
  upper (modeObservable dataSet energy mode) time

NoPositiveSubgapMode :
  ∀ {Observable Energy Bound} →
  ReconstructedClusteringSpectrum Observable Energy Bound → Set
NoPositiveSubgapMode dataSet = ∀ energy →
  PositiveEnergy dataSet energy →
  StrictlyBelow dataSet energy (gapCandidate dataSet) →
  SubgapMode dataSet energy → Empty

subgapModeClusteringExcludesPositiveSubgapMode :
  ∀ {Observable Energy Bound}
    (dataSet : ReconstructedClusteringSpectrum Observable Energy Bound) →
  SubgapModeClusteringUpper dataSet →
  NoPositiveSubgapMode dataSet
subgapModeClusteringExcludesPositiveSubgapMode dataSet clusteringUpper
  energy positive below mode =
  slowSubgapEnvelopeContradictsFastClustering dataSet
    energy mode positive below
    (spectralRepresentationLowerBound dataSet energy mode)
    (clusteringUpper energy mode)

exponentialClusteringExcludesPositiveSubgapMode :
  ∀ {Observable Energy Bound}
    (dataSet : ReconstructedClusteringSpectrum Observable Energy Bound) →
  ClusteringUpperBound dataSet →
  NoPositiveSubgapMode dataSet
exponentialClusteringExcludesPositiveSubgapMode dataSet clusteringUpper =
  subgapModeClusteringExcludesPositiveSubgapMode dataSet
    (globalClusteringUpperImpliesSubgapModeUpper dataSet clusteringUpper)

------------------------------------------------------------------------
-- Least-privilege positive spectral-gap core.
--
-- The actual spectral statement is positivity of the selected threshold plus
-- absence of positive spectrum below it.  Storing the global clustering theorem
-- in the result is convenient provenance but not mathematical gap content.
------------------------------------------------------------------------

record PositiveTransferGapCore
    {Observable Energy Bound : Set}
    (dataSet : ReconstructedClusteringSpectrum Observable Energy Bound) : Set₁ where
  field
    gapCandidatePositive : PositiveEnergy dataSet (gapCandidate dataSet)
    noPositiveSubgapMode : NoPositiveSubgapMode dataSet

open PositiveTransferGapCore public

positiveTransferGapCoreFromModeTests :
  ∀ {Observable Energy Bound}
    (dataSet : ReconstructedClusteringSpectrum Observable Energy Bound) →
  SubgapModeClusteringUpper dataSet →
  PositiveEnergy dataSet (gapCandidate dataSet) →
  PositiveTransferGapCore dataSet
positiveTransferGapCoreFromModeTests dataSet upper positiveGap = record
  { gapCandidatePositive = positiveGap
  ; noPositiveSubgapMode =
      subgapModeClusteringExcludesPositiveSubgapMode dataSet upper
  }

record PositiveTransferGap
    {Observable Energy Bound : Set}
    (dataSet : ReconstructedClusteringSpectrum Observable Energy Bound) : Set₁ where
  field
    clusteringUpperBound : ClusteringUpperBound dataSet
    gapCandidatePositive : PositiveEnergy dataSet (gapCandidate dataSet)
    noPositiveSubgapMode : NoPositiveSubgapMode dataSet

open PositiveTransferGap public

positiveTransferGapFromClusteringCutset :
  ∀ {Observable Energy Bound}
    (dataSet : ReconstructedClusteringSpectrum Observable Energy Bound) →
  ClusteringUpperBound dataSet →
  PositiveEnergy dataSet (gapCandidate dataSet) →
  PositiveTransferGap dataSet
positiveTransferGapFromClusteringCutset dataSet upper positiveGap = record
  { clusteringUpperBound = upper
  ; gapCandidatePositive = positiveGap
  ; noPositiveSubgapMode =
      exponentialClusteringExcludesPositiveSubgapMode dataSet upper
  }

positiveTransferGapCoreFromFull :
  ∀ {Observable Energy Bound}
    {dataSet : ReconstructedClusteringSpectrum Observable Energy Bound} →
  PositiveTransferGap dataSet → PositiveTransferGapCore dataSet
positiveTransferGapCoreFromFull full = record
  { gapCandidatePositive = PositiveTransferGap.gapCandidatePositive full
  ; noPositiveSubgapMode = PositiveTransferGap.noPositiveSubgapMode full
  }

record OS4SpectralInterpretation
    {Measure Schwinger Observable Energy Bound : Set}
    (closure : Limit.FiniteToContinuumOSClosure Measure Schwinger)
    (spectrum : ReconstructedClusteringSpectrum Observable Energy Bound) : Set₁ where
  field
    closureClusteringMeaning :
      Limit.Clustered closure
        (Limit.schwinger closure (Limit.continuumMeasure closure)) →
      ClusteringUpperBound spectrum

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
    (closureClusteringMeaning interpretation clustered)
    (candidateGapPositive interpretation)

clusteringSpectralContradictionAssemblyLevel : ProofLevel
clusteringSpectralContradictionAssemblyLevel = machineChecked

subgapModeClusteringConsumerReductionLevel : ProofLevel
subgapModeClusteringConsumerReductionLevel = machineChecked

positiveTransferGapCoreAssemblyLevel : ProofLevel
positiveTransferGapCoreAssemblyLevel = machineChecked

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
