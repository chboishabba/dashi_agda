{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanO4SubgapModeClusteringRound278Exact where

------------------------------------------------------------------------
-- ROUND278 / LEAST-PRIVILEGE O(4) TRANSPORT FOR THE SPECTRAL CONSUMER
--
-- R277 shows that the gap contradiction never needs a clustering upper for the
-- whole observable algebra.  It only tests the observable associated to a
-- hypothetical positive subgap mode.  Therefore R276's all-observable O(4)
-- transport is a stronger optional producer.
--
-- This owner transports the R272 continuum spatial bound only for those mode
-- observables.  The remaining representation fields are exact same-object
-- meanings, not analytic estimates.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base as ℚ using (ℚ; _*_; _≤_)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanFiniteInfluenceRowMassPowerExact as Power
import DASHI.Physics.YangMills.BalabanUnifiedPolymerSchwingerNormExact as Unified
import DASHI.Physics.YangMills.BalabanUnifiedCorrelationClusteringLimitRound272Exact as R272
import DASHI.Physics.YangMills.BalabanClayT5OS1RotationRestorationExact as OS1
import DASHI.Physics.YangMills.BalabanClayT5ClusteringToTransferGapExact as Gap

record O4SubgapModeCorrelationMeaning
    {Translation Rotation SpectralObservable Energy : Set}
    (trajectory : Unified.QuantitativeCorrelationDecayTrajectory)
    (completion : R272.SameCorrelationTrajectoryCompletion trajectory)
    (assembly : OS1.EuclideanCovarianceAssembly
      Translation Rotation (Unified.Observable trajectory) ℚ)
    (spectrum : Gap.ReconstructedClusteringSpectrum
      SpectralObservable Energy ℚ) : Set₁ where
  field
    origin : ∀ energy → Gap.SubgapMode spectrum energy →
      Unified.Observable trajectory
    spatialCopy temporalCopy : ∀ energy → Gap.SubgapMode spectrum energy →
      Nat → Unified.Observable trajectory
    pairObservable :
      Unified.Observable trajectory → Unified.Observable trajectory →
      Unified.Observable trajectory

    spatialToTemporalRotation : Rotation
    spatialToTemporalRotationIsFull :
      OS1.FullRotation (OS1.rotationData assembly) spatialToTemporalRotation

    rotatedSpatialModePairIsTemporal : ∀ energy mode time →
      OS1.rotate (OS1.rotationData assembly) spatialToTemporalRotation
        (pairObservable (origin energy mode) (spatialCopy energy mode time))
      ≡ pairObservable (origin energy mode) (temporalCopy energy mode time)

    spatialModeDistanceIsTime : ∀ energy mode time →
      Unified.physicalDistance trajectory
        (origin energy mode) (spatialCopy energy mode time)
      ≡ time

    spatialModeConnectedMeaning : ∀ energy mode time →
      Unified.connectedCorrelationMagnitude trajectory
        (R272.correlationLimit completion)
        (origin energy mode) (spatialCopy energy mode time)
      ≡ OS1.correlator assembly
          (pairObservable (origin energy mode) (spatialCopy energy mode time))

    temporalModeSpectralMeaning : ∀ energy mode time →
      Gap.connectedCorrelation spectrum
        (Gap.modeObservable spectrum energy mode) time
      ≡ OS1.correlator assembly
          (pairObservable (origin energy mode) (temporalCopy energy mode time))

    modeEnvelopeMeaning : ∀ energy mode time →
      Gap.clusteringEnvelope spectrum
        (Gap.modeObservable spectrum energy mode) time
      ≡ Unified.amplitude trajectory
          * Power.rationalPower (Unified.ratio trajectory) time

    spectralOrderMeaning : ∀ left right →
      Gap.LessEqual spectrum left right ≡ (left ≤ right)

open O4SubgapModeCorrelationMeaning public

spatialModeBoundAtTime :
  ∀ {Translation Rotation SpectralObservable Energy}
    {trajectory : Unified.QuantitativeCorrelationDecayTrajectory}
    {completion : R272.SameCorrelationTrajectoryCompletion trajectory}
    {assembly : OS1.EuclideanCovarianceAssembly
      Translation Rotation (Unified.Observable trajectory) ℚ}
    {spectrum : Gap.ReconstructedClusteringSpectrum
      SpectralObservable Energy ℚ}
    (meaning : O4SubgapModeCorrelationMeaning
      trajectory completion assembly spectrum)
    energy mode time →
  Unified.connectedCorrelationMagnitude trajectory
    (R272.correlationLimit completion)
    (origin meaning energy mode) (spatialCopy meaning energy mode time)
  ≤ Unified.amplitude trajectory
      * Power.rationalPower (Unified.ratio trajectory) time
spatialModeBoundAtTime {trajectory = trajectory} {completion = completion}
  meaning energy mode time =
  subst
    (λ distance →
      Unified.connectedCorrelationMagnitude trajectory
        (R272.correlationLimit completion)
        (origin meaning energy mode) (spatialCopy meaning energy mode time)
      ≤ Unified.amplitude trajectory
          * Power.rationalPower (Unified.ratio trajectory) distance)
    (spatialModeDistanceIsTime meaning energy mode time)
    (R272.limitCorrelationBound trajectory completion
      (origin meaning energy mode) (spatialCopy meaning energy mode time))

spatialTemporalModeCorrelatorEqual :
  ∀ {Translation Rotation SpectralObservable Energy}
    {trajectory : Unified.QuantitativeCorrelationDecayTrajectory}
    {completion : R272.SameCorrelationTrajectoryCompletion trajectory}
    {assembly : OS1.EuclideanCovarianceAssembly
      Translation Rotation (Unified.Observable trajectory) ℚ}
    {spectrum : Gap.ReconstructedClusteringSpectrum
      SpectralObservable Energy ℚ}
    (meaning : O4SubgapModeCorrelationMeaning
      trajectory completion assembly spectrum)
    energy mode time →
  OS1.correlator assembly
      (pairObservable (origin meaning energy mode) (temporalCopy meaning energy mode time))
  ≡ OS1.correlator assembly
      (pairObservable (origin meaning energy mode) (spatialCopy meaning energy mode time))
spatialTemporalModeCorrelatorEqual {assembly = assembly}
  meaning energy mode time =
  trans
    (sym (cong (OS1.correlator assembly)
      (rotatedSpatialModePairIsTemporal meaning energy mode time)))
    (OS1.assembledRotationCovariance assembly
      (spatialToTemporalRotation meaning)
      (pairObservable
        (origin meaning energy mode) (spatialCopy meaning energy mode time))
      (spatialToTemporalRotationIsFull meaning))

subgapModeTemporalClusteringUpper :
  ∀ {Translation Rotation SpectralObservable Energy}
    {trajectory : Unified.QuantitativeCorrelationDecayTrajectory}
    {completion : R272.SameCorrelationTrajectoryCompletion trajectory}
    {assembly : OS1.EuclideanCovarianceAssembly
      Translation Rotation (Unified.Observable trajectory) ℚ}
    {spectrum : Gap.ReconstructedClusteringSpectrum
      SpectralObservable Energy ℚ} →
  O4SubgapModeCorrelationMeaning trajectory completion assembly spectrum →
  Gap.SubgapModeClusteringUpper spectrum
subgapModeTemporalClusteringUpper
  {trajectory = trajectory}
  {completion = completion}
  {assembly = assembly}
  {spectrum = spectrum}
  meaning energy mode time =
  subst
    (λ proposition → proposition)
    (sym (spectralOrderMeaning meaning
      (Gap.connectedCorrelation spectrum (Gap.modeObservable spectrum energy mode) time)
      (Gap.clusteringEnvelope spectrum (Gap.modeObservable spectrum energy mode) time)))
    (subst
      (λ left → left
        ≤ Unified.amplitude trajectory
            * Power.rationalPower (Unified.ratio trajectory) time)
      (trans
        (temporalModeSpectralMeaning meaning energy mode time)
        (spatialTemporalModeCorrelatorEqual meaning energy mode time))
      (subst
        (λ left → left
          ≤ Unified.amplitude trajectory
              * Power.rationalPower (Unified.ratio trajectory) time)
        (sym (spatialModeConnectedMeaning meaning energy mode time))
        (spatialModeBoundAtTime meaning energy mode time)))

round278SubgapModeO4CompilerLevel : ProofLevel
round278SubgapModeO4CompilerLevel = machineChecked

-- Literal representation/geometry seam.  Only the spectrally separating mode
-- family is now required; no global all-observable clustering meaning is owed.
round278PhysicalSubgapModeSameObjectMeaningLevel : ProofLevel
round278PhysicalSubgapModeSameObjectMeaningLevel = conditional
