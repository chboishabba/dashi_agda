module DASHI.Physics.YangMills.BalabanClayT5OSReconstructionCyclicityExact where

open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Sigma using (Σ; fst; snd)
open import Data.Product using (_×_; proj₁; proj₂)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanClayT5ClusteringToTransferGapExact as Gap

------------------------------------------------------------------------
-- Primary provenance.
--
-- Helmut Reeh and Siegfried Schlieder,
-- "Bemerkungen zur Unitaraquivalenz von Lorentzinvarianten Feldern",
-- Il Nuovo Cimento 22 (1961), 1051--1068.
-- DOI: 10.1007/BF02787889.
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
-- The exact interface used below is weaker than a full local-net
-- Reeh--Schlieder theorem: the positive-time OS cylinder vectors need only
-- detect every nonzero reconstructed subgap vector. This is the precise
-- overlap premise consumed by the clustering-to-gap contradiction.
------------------------------------------------------------------------

record PositiveTimeVacuumCyclicity (Observable Vector : Set) : Set₁ where
  field
    vacuum : Vector
    vectorOfObservable : Observable → Vector
    PositiveTimeObservable : Observable → Set
    NonzeroVector : Vector → Set
    Overlap : Vector → Vector → Set

    cyclicityDetectsNonzeroVector : ∀ vector →
      NonzeroVector vector →
      Σ Observable (λ observable →
        PositiveTimeObservable observable
        × Overlap (vectorOfObservable observable) vector)

open PositiveTimeVacuumCyclicity public

record ReconstructedSubgapVectors (Energy Vector : Set) : Set₁ where
  field
    SubgapMode : Energy → Set
    modeVector : ∀ energy → SubgapMode energy → Vector
    NonzeroVectorWitness : ∀ energy → SubgapMode energy → Set
    modeVectorNonzero : ∀ energy mode → NonzeroVectorWitness energy mode

open ReconstructedSubgapVectors public

record CyclicSubgapVectorMeaning
    {Observable Energy Vector : Set}
    (cyclicity : PositiveTimeVacuumCyclicity Observable Vector)
    (subgap : ReconstructedSubgapVectors Energy Vector) : Set₁ where
  field
    nonzeroMeaning : ∀ energy mode →
      NonzeroVectorWitness subgap energy mode →
      NonzeroVector cyclicity (modeVector subgap energy mode)

open CyclicSubgapVectorMeaning public

modeDetectionWitness :
  ∀ {Observable Energy Vector}
    {cyclicity : PositiveTimeVacuumCyclicity Observable Vector}
    {subgap : ReconstructedSubgapVectors Energy Vector} →
  CyclicSubgapVectorMeaning cyclicity subgap →
  ∀ energy (mode : SubgapMode subgap energy) →
  Σ Observable (λ observable →
    PositiveTimeObservable cyclicity observable
    × Overlap cyclicity
        (vectorOfObservable cyclicity observable)
        (modeVector subgap energy mode))
modeDetectionWitness {cyclicity = cyclicity} {subgap = subgap} meaning
  energy mode =
  cyclicityDetectsNonzeroVector cyclicity
    (modeVector subgap energy mode)
    (nonzeroMeaning meaning energy mode
      (modeVectorNonzero subgap energy mode))

modeObservableFromCyclicity :
  ∀ {Observable Energy Vector}
    {cyclicity : PositiveTimeVacuumCyclicity Observable Vector}
    {subgap : ReconstructedSubgapVectors Energy Vector} →
  CyclicSubgapVectorMeaning cyclicity subgap →
  ∀ energy → SubgapMode subgap energy → Observable
modeObservableFromCyclicity meaning energy mode =
  fst (modeDetectionWitness meaning energy mode)

modeObservableIsPositiveTime :
  ∀ {Observable Energy Vector}
    {cyclicity : PositiveTimeVacuumCyclicity Observable Vector}
    {subgap : ReconstructedSubgapVectors Energy Vector}
    (meaning : CyclicSubgapVectorMeaning cyclicity subgap) →
  ∀ energy (mode : SubgapMode subgap energy) →
  PositiveTimeObservable cyclicity
    (modeObservableFromCyclicity meaning energy mode)
modeObservableIsPositiveTime meaning energy mode =
  proj₁ (snd (modeDetectionWitness meaning energy mode))

modeObservableOverlapsSubgapVector :
  ∀ {Observable Energy Vector}
    {cyclicity : PositiveTimeVacuumCyclicity Observable Vector}
    {subgap : ReconstructedSubgapVectors Energy Vector}
    (meaning : CyclicSubgapVectorMeaning cyclicity subgap) →
  ∀ energy (mode : SubgapMode subgap energy) →
  Overlap cyclicity
    (vectorOfObservable cyclicity
      (modeObservableFromCyclicity meaning energy mode))
    (modeVector subgap energy mode)
modeObservableOverlapsSubgapVector meaning energy mode =
  proj₂ (snd (modeDetectionWitness meaning energy mode))

record CyclicReconstructedClusteringSpectrum
    (Observable Energy Bound Vector : Set) : Set₁ where
  field
    cyclicity : PositiveTimeVacuumCyclicity Observable Vector
    subgapVectors : ReconstructedSubgapVectors Energy Vector
    subgapMeaning : CyclicSubgapVectorMeaning cyclicity subgapVectors

    zeroEnergy gapCandidate : Energy
    PositiveEnergy : Energy → Set
    StrictlyBelow : Energy → Energy → Set

    connectedCorrelation : Observable → Nat → Bound
    clusteringEnvelope : Observable → Nat → Bound
    subgapSpectralEnvelope : Energy → Observable → Nat → Bound
    LessEqual : Bound → Bound → Set

    spectralRepresentationLowerBoundFromOverlap :
      ∀ energy (mode : SubgapMode subgapVectors energy) time →
      Overlap cyclicity
        (vectorOfObservable cyclicity
          (modeObservableFromCyclicity subgapMeaning energy mode))
        (modeVector subgapVectors energy mode) →
      LessEqual
        (subgapSpectralEnvelope energy
          (modeObservableFromCyclicity subgapMeaning energy mode) time)
        (connectedCorrelation
          (modeObservableFromCyclicity subgapMeaning energy mode) time)

    slowSubgapEnvelopeContradictsFastClustering :
      ∀ energy (mode : SubgapMode subgapVectors energy) →
      PositiveEnergy energy → StrictlyBelow energy gapCandidate →
      (∀ time →
        LessEqual
          (subgapSpectralEnvelope energy
            (modeObservableFromCyclicity subgapMeaning energy mode) time)
          (connectedCorrelation
            (modeObservableFromCyclicity subgapMeaning energy mode) time)) →
      (∀ time →
        LessEqual
          (connectedCorrelation
            (modeObservableFromCyclicity subgapMeaning energy mode) time)
          (clusteringEnvelope
            (modeObservableFromCyclicity subgapMeaning energy mode) time)) →
      Gap.Empty

open CyclicReconstructedClusteringSpectrum public

asReconstructedClusteringSpectrum :
  ∀ {Observable Energy Bound Vector} →
  CyclicReconstructedClusteringSpectrum Observable Energy Bound Vector →
  Gap.ReconstructedClusteringSpectrum Observable Energy Bound
asReconstructedClusteringSpectrum dataSet = record
  { Gap.ReconstructedClusteringSpectrum.zeroEnergy = zeroEnergy dataSet
  ; Gap.ReconstructedClusteringSpectrum.gapCandidate = gapCandidate dataSet
  ; Gap.ReconstructedClusteringSpectrum.PositiveEnergy = PositiveEnergy dataSet
  ; Gap.ReconstructedClusteringSpectrum.StrictlyBelow = StrictlyBelow dataSet
  ; Gap.ReconstructedClusteringSpectrum.connectedCorrelation =
      connectedCorrelation dataSet
  ; Gap.ReconstructedClusteringSpectrum.clusteringEnvelope =
      clusteringEnvelope dataSet
  ; Gap.ReconstructedClusteringSpectrum.subgapSpectralEnvelope =
      subgapSpectralEnvelope dataSet
  ; Gap.ReconstructedClusteringSpectrum.LessEqual = LessEqual dataSet
  ; Gap.ReconstructedClusteringSpectrum.SubgapMode =
      SubgapMode (subgapVectors dataSet)
  ; Gap.ReconstructedClusteringSpectrum.modeObservable =
      modeObservableFromCyclicity (subgapMeaning dataSet)
  ; Gap.ReconstructedClusteringSpectrum.spectralRepresentationLowerBound =
      λ energy mode time →
        spectralRepresentationLowerBoundFromOverlap dataSet energy mode time
          (modeObservableOverlapsSubgapVector
            (subgapMeaning dataSet) energy mode)
  ; Gap.ReconstructedClusteringSpectrum.slowSubgapEnvelopeContradictsFastClustering =
      slowSubgapEnvelopeContradictsFastClustering dataSet
  }

osVacuumCyclicityToObservableChoiceLevel : ProofLevel
osVacuumCyclicityToObservableChoiceLevel = machineChecked

cyclicityToSubgapOverlapLevel : ProofLevel
cyclicityToSubgapOverlapLevel = machineChecked

cyclicSpectrumAdapterLevel : ProofLevel
cyclicSpectrumAdapterLevel = machineChecked

physicalPositiveTimeCylinderCyclicityInputsLevel : ProofLevel
physicalPositiveTimeCylinderCyclicityInputsLevel = conditional

physicalSubgapVectorNonzeroMeaningInputsLevel : ProofLevel
physicalSubgapVectorNonzeroMeaningInputsLevel = conditional

physicalSpectralLowerBoundFromOverlapInputsLevel : ProofLevel
physicalSpectralLowerBoundFromOverlapInputsLevel = conditional
