{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanO4SpatialToTemporalClusteringRound276Exact where

------------------------------------------------------------------------
-- ROUND276 / DISCHARGE THE SPATIAL->TEMPORAL WRONGTYPE WITH OS1/O(4)
--
-- The R273/R272 quantitative trajectory is a two-observable spatial decay
-- theorem.  The R274/R275 mass-gap consumer is a Euclidean-time connected
-- correlator bound on the reconstructed continuum spectral family.  Those are
-- not definitionally the same object.
--
-- The missing conversion is nevertheless structural once continuum OS1 is
-- available: rotate a pair separated along a spatial axis into the same pair
-- separated along Euclidean time.  Full O(4) covariance preserves the
-- correlator, and the 90-degree axis rotation preserves the separation length.
--
-- This file proves exactly that adapter.  It does NOT identify a finite/RG
-- correlator with a continuum one; R272's same-correlation completion is still
-- required first.  It also does not infer OS1 from a label: it consumes the
-- concrete EuclideanCovarianceAssembly and a literal FullRotation witness.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base as ℚ using (ℚ; _*_; _≤_)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanFiniteInfluenceRowMassPowerExact as Power
import DASHI.Physics.YangMills.BalabanUnifiedPolymerSchwingerNormExact as Unified
import DASHI.Physics.YangMills.BalabanUnifiedCorrelationClusteringLimitRound272Exact as R272
import DASHI.Physics.YangMills.BalabanClayT5OS1RotationRestorationExact as OS1
import DASHI.Physics.YangMills.BalabanClayT5ClusteringToTransferGapExact as Gap

record O4SpatialToTemporalCorrelationMeaning
    {Translation Rotation SpectralObservable Energy : Set}
    (trajectory : Unified.QuantitativeCorrelationDecayTrajectory)
    (completion : R272.SameCorrelationTrajectoryCompletion trajectory)
    (assembly : OS1.EuclideanCovarianceAssembly
      Translation Rotation (Unified.Observable trajectory) ℚ)
    (spectrum : Gap.ReconstructedClusteringSpectrum
      SpectralObservable Energy ℚ) : Set₁ where
  field
    -- A spectral observable is represented by a same-family continuum
    -- observable at the origin, together with spatial/time translated copies.
    origin : SpectralObservable → Unified.Observable trajectory
    spatialCopy temporalCopy :
      SpectralObservable → Nat → Unified.Observable trajectory
    pairObservable :
      Unified.Observable trajectory → Unified.Observable trajectory →
      Unified.Observable trajectory

    -- One literal full O(4) rotation sends the spatial axis to Euclidean time.
    spatialToTemporalRotation : Rotation
    spatialToTemporalRotationIsFull :
      OS1.FullRotation (OS1.rotationData assembly) spatialToTemporalRotation

    rotatedSpatialPairIsTemporalPair : ∀ observable time →
      OS1.rotate (OS1.rotationData assembly) spatialToTemporalRotation
        (pairObservable (origin observable) (spatialCopy observable time))
      ≡ pairObservable (origin observable) (temporalCopy observable time)

    -- The spatial support metric used by the quantitative trajectory is the
    -- integer Euclidean separation parameter consumed by the spectral family.
    spatialDistanceIsTime : ∀ observable time →
      Unified.physicalDistance trajectory
        (origin observable) (spatialCopy observable time)
      ≡ time

    -- Same-object meanings.  These are representation welds, not estimates.
    spatialConnectedMeaning : ∀ observable time →
      Unified.connectedCorrelationMagnitude trajectory
        (R272.correlationLimit completion)
        (origin observable) (spatialCopy observable time)
      ≡ OS1.correlator assembly
          (pairObservable (origin observable) (spatialCopy observable time))

    temporalSpectralMeaning : ∀ observable time →
      Gap.connectedCorrelation spectrum observable time
      ≡ OS1.correlator assembly
          (pairObservable (origin observable) (temporalCopy observable time))

    spectralEnvelopeMeaning : ∀ observable time →
      Gap.clusteringEnvelope spectrum observable time
      ≡ Unified.amplitude trajectory
          * Power.rationalPower (Unified.ratio trajectory) time

    -- The spectral order is the ordinary rational order on this quantitative
    -- carrier.  Keeping this literal prevents an opaque Bound adapter.
    spectralOrderMeaning : ∀ left right →
      Gap.LessEqual spectrum left right ≡ (left ≤ right)

open O4SpatialToTemporalCorrelationMeaning public

spatialPairBoundAtTime :
  ∀ {Translation Rotation SpectralObservable Energy}
    {trajectory : Unified.QuantitativeCorrelationDecayTrajectory}
    {completion : R272.SameCorrelationTrajectoryCompletion trajectory}
    {assembly : OS1.EuclideanCovarianceAssembly
      Translation Rotation (Unified.Observable trajectory) ℚ}
    {spectrum : Gap.ReconstructedClusteringSpectrum
      SpectralObservable Energy ℚ}
    (meaning : O4SpatialToTemporalCorrelationMeaning
      trajectory completion assembly spectrum)
    observable time →
  Unified.connectedCorrelationMagnitude trajectory
    (R272.correlationLimit completion)
    (origin meaning observable) (spatialCopy meaning observable time)
  ≤ Unified.amplitude trajectory
      * Power.rationalPower (Unified.ratio trajectory) time
spatialPairBoundAtTime {trajectory = trajectory} {completion = completion}
  meaning observable time =
  subst
    (λ distance →
      Unified.connectedCorrelationMagnitude trajectory
        (R272.correlationLimit completion)
        (origin meaning observable) (spatialCopy meaning observable time)
      ≤ Unified.amplitude trajectory
          * Power.rationalPower (Unified.ratio trajectory) distance)
    (spatialDistanceIsTime meaning observable time)
    (R272.limitCorrelationBound trajectory completion
      (origin meaning observable) (spatialCopy meaning observable time))

spatialTemporalCorrelatorEqual :
  ∀ {Translation Rotation SpectralObservable Energy}
    {trajectory : Unified.QuantitativeCorrelationDecayTrajectory}
    {completion : R272.SameCorrelationTrajectoryCompletion trajectory}
    {assembly : OS1.EuclideanCovarianceAssembly
      Translation Rotation (Unified.Observable trajectory) ℚ}
    {spectrum : Gap.ReconstructedClusteringSpectrum
      SpectralObservable Energy ℚ}
    (meaning : O4SpatialToTemporalCorrelationMeaning
      trajectory completion assembly spectrum)
    observable time →
  OS1.correlator assembly
      (pairObservable (origin meaning observable) (temporalCopy meaning observable time))
  ≡ OS1.correlator assembly
      (pairObservable (origin meaning observable) (spatialCopy meaning observable time))
spatialTemporalCorrelatorEqual {assembly = assembly} meaning observable time =
  trans
    (sym (cong (OS1.correlator assembly)
      (rotatedSpatialPairIsTemporalPair meaning observable time)))
    (OS1.assembledRotationCovariance assembly
      (spatialToTemporalRotation meaning)
      (pairObservable (origin meaning observable) (spatialCopy meaning observable time))
      (spatialToTemporalRotationIsFull meaning))

quantitativeTemporalClusteringUpper :
  ∀ {Translation Rotation SpectralObservable Energy}
    {trajectory : Unified.QuantitativeCorrelationDecayTrajectory}
    {completion : R272.SameCorrelationTrajectoryCompletion trajectory}
    {assembly : OS1.EuclideanCovarianceAssembly
      Translation Rotation (Unified.Observable trajectory) ℚ}
    {spectrum : Gap.ReconstructedClusteringSpectrum
      SpectralObservable Energy ℚ} →
  O4SpatialToTemporalCorrelationMeaning trajectory completion assembly spectrum →
  Gap.ClusteringUpperBound spectrum
quantitativeTemporalClusteringUpper
  {trajectory = trajectory}
  {completion = completion}
  {assembly = assembly}
  {spectrum = spectrum}
  meaning observable time =
  subst
    (λ proposition → proposition)
    (sym (spectralOrderMeaning meaning
      (Gap.connectedCorrelation spectrum observable time)
      (Gap.clusteringEnvelope spectrum observable time)))
    (subst
      (λ left → left
        ≤ Unified.amplitude trajectory
            * Power.rationalPower (Unified.ratio trajectory) time)
      (trans
        (temporalSpectralMeaning meaning observable time)
        (spatialTemporalCorrelatorEqual meaning observable time))
      (subst
        (λ left → left
          ≤ Unified.amplitude trajectory
              * Power.rationalPower (Unified.ratio trajectory) time)
        (sym (spatialConnectedMeaning meaning observable time))
        (spatialPairBoundAtTime meaning observable time)))

round276SpatialToTemporalO4CompilerLevel : ProofLevel
round276SpatialToTemporalO4CompilerLevel = machineChecked

-- Geometry/representation seam: instantiate the full axis rotation and identify
-- the spatial and temporal two-insertion observables on the same continuum
-- family.  This is a WrongType bridge, not a new decay estimate.
round276PhysicalSpatialTemporalSameObjectMeaningLevel : ProofLevel
round276PhysicalSpatialTemporalSameObjectMeaningLevel = conditional

-- Reuse R272 continuum completion and OS1 restoration.  Neither is repaid as a
-- separate B-specific theorem by this adapter.
round276SameCorrelationCompletionLevel : ProofLevel
round276SameCorrelationCompletionLevel =
  R272.round272SameCorrelationTrajectoryCompletionLevel

round276PhysicalO4RestorationLevel : ProofLevel
round276PhysicalO4RestorationLevel = OS1.physicalOS1PredicateMeaningInputsLevel
