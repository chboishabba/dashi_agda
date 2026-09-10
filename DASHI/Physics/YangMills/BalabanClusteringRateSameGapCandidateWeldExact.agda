{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanClusteringRateSameGapCandidateWeldExact where

------------------------------------------------------------------------
-- CLUSTERING RATE = GAP-CANDIDATE SAME-OBJECT WELD
--
-- The older OS mass-gap producer already carries one strictly positive physical
-- clustering rate `mStar` and builds the Hamiltonian spectrum gap at exactly
-- that same threshold.  The newer least-privilege spectrum carrier made Energy
-- abstract and therefore stores positivity of `gapCandidate` as a separate
-- field.
--
-- On the direct clustering-rate route there is no second Yang--Mills theorem:
-- choose the energy-threshold carrier to be the same Bound carrier, set
--
--   gapCandidate = mStar,
--
-- and reuse `mStarPositive` definitionally.  What remains spectral is the
-- standard lower-envelope / overlap / slow-versus-fast contradiction authority,
-- not positivity of a newly invented number.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.YangMills.BalabanOSReconstructionMassGapProduction as OS
import DASHI.Physics.YangMills.BalabanClayT5ClusteringToTransferGapExact as Gap

record SameRateReconstructedSpectrumData
    (Observable Scalar Bound Hamiltonian : Set)
    (decay : OS.UniformConnectedCorrelationDecayData
      Observable Nat Scalar Bound Hamiltonian) : Set₁ where
  field
    zeroEnergy : Bound
    StrictlyBelow : Bound → Bound → Set

    subgapSpectralEnvelope : Bound → Observable → Nat → Bound
    SubgapMode : Bound → Set
    modeObservable : ∀ energy → SubgapMode energy → Observable

    spectralRepresentationLowerBound : ∀ energy mode time →
      OS.LessEqual decay
        (subgapSpectralEnvelope energy (modeObservable energy mode) time)
        (OS.absoluteValue decay
          (OS.connectedCorrelation decay
            (modeObservable energy mode)
            (modeObservable energy mode)
            time))

    slowSubgapEnvelopeContradictsFastClustering : ∀ energy mode →
      OS.Positive decay energy →
      StrictlyBelow energy (OS.mStar decay) →
      (∀ time →
        OS.LessEqual decay
          (subgapSpectralEnvelope energy (modeObservable energy mode) time)
          (OS.absoluteValue decay
            (OS.connectedCorrelation decay
              (modeObservable energy mode)
              (modeObservable energy mode)
              time))) →
      (∀ time →
        OS.LessEqual decay
          (OS.absoluteValue decay
            (OS.connectedCorrelation decay
              (modeObservable energy mode)
              (modeObservable energy mode)
              time))
          (OS.multiply decay
            (OS.correlationConstant decay
              (modeObservable energy mode)
              (modeObservable energy mode))
            (OS.exponentialDecay decay (OS.mStar decay) time))) →
      Gap.Empty

open SameRateReconstructedSpectrumData public

asReconstructedClusteringSpectrum :
  ∀ {Observable Scalar Bound Hamiltonian}
    {decay : OS.UniformConnectedCorrelationDecayData
      Observable Nat Scalar Bound Hamiltonian} →
  SameRateReconstructedSpectrumData Observable Scalar Bound Hamiltonian decay →
  Gap.ReconstructedClusteringSpectrum Observable Bound Bound
asReconstructedClusteringSpectrum {decay = decay} dataSet = record
  { Gap.zeroEnergy = zeroEnergy dataSet
  ; Gap.gapCandidate = OS.mStar decay
  ; Gap.PositiveEnergy = OS.Positive decay
  ; Gap.StrictlyBelow = StrictlyBelow dataSet
  ; Gap.connectedCorrelation = λ observable time →
      OS.absoluteValue decay
        (OS.connectedCorrelation decay observable observable time)
  ; Gap.clusteringEnvelope = λ observable time →
      OS.multiply decay
        (OS.correlationConstant decay observable observable)
        (OS.exponentialDecay decay (OS.mStar decay) time)
  ; Gap.subgapSpectralEnvelope = subgapSpectralEnvelope dataSet
  ; Gap.LessEqual = OS.LessEqual decay
  ; Gap.SubgapMode = SubgapMode dataSet
  ; Gap.modeObservable = modeObservable dataSet
  ; Gap.spectralRepresentationLowerBound = spectralRepresentationLowerBound dataSet
  ; Gap.slowSubgapEnvelopeContradictsFastClustering =
      slowSubgapEnvelopeContradictsFastClustering dataSet
  }

sameRateGapCandidatePositive :
  ∀ {Observable Scalar Bound Hamiltonian}
    {decay : OS.UniformConnectedCorrelationDecayData
      Observable Nat Scalar Bound Hamiltonian}
    (dataSet : SameRateReconstructedSpectrumData
      Observable Scalar Bound Hamiltonian decay) →
  Gap.PositiveEnergy (asReconstructedClusteringSpectrum dataSet)
    (Gap.gapCandidate (asReconstructedClusteringSpectrum dataSet))
sameRateGapCandidatePositive {decay = decay} dataSet =
  OS.mStarPositive decay

sameRateSubgapClusteringUpper :
  ∀ {Observable Scalar Bound Hamiltonian}
    {decay : OS.UniformConnectedCorrelationDecayData
      Observable Nat Scalar Bound Hamiltonian}
    (dataSet : SameRateReconstructedSpectrumData
      Observable Scalar Bound Hamiltonian decay) →
  Gap.SubgapModeClusteringUpper (asReconstructedClusteringSpectrum dataSet)
sameRateSubgapClusteringUpper {decay = decay} dataSet energy mode time =
  OS.uniformConnectedCorrelationDecay decay
    (modeObservable dataSet energy mode)
    (modeObservable dataSet energy mode)
    time

sameRatePositiveTransferGapCore :
  ∀ {Observable Scalar Bound Hamiltonian}
    {decay : OS.UniformConnectedCorrelationDecayData
      Observable Nat Scalar Bound Hamiltonian}
    (dataSet : SameRateReconstructedSpectrumData
      Observable Scalar Bound Hamiltonian decay) →
  Gap.PositiveTransferGapCore (asReconstructedClusteringSpectrum dataSet)
sameRatePositiveTransferGapCore dataSet =
  Gap.positiveTransferGapCoreFromModeTests
    (asReconstructedClusteringSpectrum dataSet)
    (sameRateSubgapClusteringUpper dataSet)
    (sameRateGapCandidatePositive dataSet)

------------------------------------------------------------------------
-- Boundary.
------------------------------------------------------------------------

positiveGapCandidateIndependentYMAnalyticLeafOnSameRateRoute : Bool
positiveGapCandidateIndependentYMAnalyticLeafOnSameRateRoute = false

clusteringRateAndGapCandidateSameObject : Bool
clusteringRateAndGapCandidateSameObject = true

spectralRepresentationAndOverlapStillSeparate : Bool
spectralRepresentationAndOverlapStillSeparate = true

slowVersusFastSpectralComparisonStillSeparate : Bool
slowVersusFastSpectralComparisonStillSeparate = true

clayPromotion : Bool
clayPromotion = false

positiveGapCandidateIndependentYMAnalyticLeafOnSameRateRouteIsFalse :
  positiveGapCandidateIndependentYMAnalyticLeafOnSameRateRoute ≡ false
positiveGapCandidateIndependentYMAnalyticLeafOnSameRateRouteIsFalse = refl

clusteringRateAndGapCandidateSameObjectIsTrue :
  clusteringRateAndGapCandidateSameObject ≡ true
clusteringRateAndGapCandidateSameObjectIsTrue = refl

clayPromotionIsFalse : clayPromotion ≡ false
clayPromotionIsFalse = refl
