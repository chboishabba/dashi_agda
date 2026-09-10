module DASHI.Physics.YangMills.BalabanUnifiedPolymerSchwingerNormExact where

------------------------------------------------------------------------
-- ROUND65/R271/R273:
-- ONE POLYMER/SCHWINGER NORM, THREE DOWNSTREAM PROJECTIONS
-- + LEAST-PRIVILEGE DIRECT CORRELATION-DECAY SURFACE
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; suc)
open import Data.Product using (_×_)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; 1ℚ; _*_; _≤_; _<_)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanFiniteInfluenceRowMassPowerExact as Power
import DASHI.Physics.YangMills.BalabanRowCPostBC2PhysicalCompletionRound108Exact as R108

------------------------------------------------------------------------
-- Generic unified norm authority.
------------------------------------------------------------------------

record UnifiedPolymerSchwingerNormAuthority
    (State OrdinaryObservable CompositeObservable WeightedCorrelation Bound : Set)
    : Set₁ where
  field
    unifiedDistance : State → State → Bound

    ordinaryProjection : State → OrdinaryObservable
    compositeProjection : State → CompositeObservable
    correlationProjection : State → WeightedCorrelation

    ordinaryDistance : OrdinaryObservable → OrdinaryObservable → Bound
    compositeDistance : CompositeObservable → CompositeObservable → Bound
    correlationDistance : WeightedCorrelation → WeightedCorrelation → Bound

    LessEqual : Bound → Bound → Set

    ordinaryProjectionNonexpansive : ∀ left right →
      LessEqual
        (ordinaryDistance
          (ordinaryProjection left) (ordinaryProjection right))
        (unifiedDistance left right)

    compositeProjectionNonexpansive : ∀ left right →
      LessEqual
        (compositeDistance
          (compositeProjection left) (compositeProjection right))
        (unifiedDistance left right)

    correlationProjectionNonexpansive : ∀ left right →
      LessEqual
        (correlationDistance
          (correlationProjection left) (correlationProjection right))
        (unifiedDistance left right)

    transitive : ∀ {left middle right} →
      LessEqual left middle → LessEqual middle right → LessEqual left right

open UnifiedPolymerSchwingerNormAuthority public

record UnifiedRGIncrementControl
    {State OrdinaryObservable CompositeObservable WeightedCorrelation Bound : Set}
    (authority : UnifiedPolymerSchwingerNormAuthority
      State OrdinaryObservable CompositeObservable WeightedCorrelation Bound)
    : Set₁ where
  field
    stateAtScale : Nat → State
    incrementMajorant : Nat → Bound
    unifiedIncrementBound : ∀ scale →
      LessEqual authority
        (unifiedDistance authority
          (stateAtScale scale) (stateAtScale (suc scale)))
        (incrementMajorant scale)

open UnifiedRGIncrementControl public

ordinaryIncrementBound :
  ∀ {State Ordinary Composite Correlation Bound}
    {authority : UnifiedPolymerSchwingerNormAuthority
      State Ordinary Composite Correlation Bound}
    (control : UnifiedRGIncrementControl authority)
    (scale : Nat) →
  LessEqual authority
    (ordinaryDistance authority
      (ordinaryProjection authority (stateAtScale control scale))
      (ordinaryProjection authority (stateAtScale control (suc scale))))
    (incrementMajorant control scale)
ordinaryIncrementBound {authority = authority} control scale =
  transitive authority
    (ordinaryProjectionNonexpansive authority
      (stateAtScale control scale)
      (stateAtScale control (suc scale)))
    (unifiedIncrementBound control scale)

compositeIncrementBound :
  ∀ {State Ordinary Composite Correlation Bound}
    {authority : UnifiedPolymerSchwingerNormAuthority
      State Ordinary Composite Correlation Bound}
    (control : UnifiedRGIncrementControl authority)
    (scale : Nat) →
  LessEqual authority
    (compositeDistance authority
      (compositeProjection authority (stateAtScale control scale))
      (compositeProjection authority (stateAtScale control (suc scale))))
    (incrementMajorant control scale)
compositeIncrementBound {authority = authority} control scale =
  transitive authority
    (compositeProjectionNonexpansive authority
      (stateAtScale control scale)
      (stateAtScale control (suc scale)))
    (unifiedIncrementBound control scale)

correlationIncrementBound :
  ∀ {State Ordinary Composite Correlation Bound}
    {authority : UnifiedPolymerSchwingerNormAuthority
      State Ordinary Composite Correlation Bound}
    (control : UnifiedRGIncrementControl authority)
    (scale : Nat) →
  LessEqual authority
    (correlationDistance authority
      (correlationProjection authority (stateAtScale control scale))
      (correlationProjection authority (stateAtScale control (suc scale))))
    (incrementMajorant control scale)
correlationIncrementBound {authority = authority} control scale =
  transitive authority
    (correlationProjectionNonexpansive authority
      (stateAtScale control scale)
      (stateAtScale control (suc scale)))
    (unifiedIncrementBound control scale)

------------------------------------------------------------------------
-- R273 LEAST-PRIVILEGE B-FACING OBJECT.
--
-- The NS-R592 introspection forbids requiring the whole unified norm merely
-- because it is one convenient way to prove clustering.  The canonical finite
-- mass-gap producer needs only a correlation trajectory and its uniform
-- geometric inequality.  No large-field, derivative, composite, or generic
-- state-distance coordinates occur in this record.
------------------------------------------------------------------------

record QuantitativeCorrelationDecayTrajectory : Set₁ where
  field
    State Observable Correlation : Set
    correlationProjection : State → Correlation
    stateAtScale : Nat → State

    physicalDistance : Observable → Observable → Nat
    connectedCorrelationMagnitude :
      Correlation → Observable → Observable → ℚ

    amplitude ratio : ℚ
    amplitudeNonnegative : 0ℚ ≤ amplitude
    ratioNonnegative : 0ℚ ≤ ratio
    ratioStrictlyBelowOne : ratio < 1ℚ

    geometricDecayAtEveryScale : ∀ scale left right →
      connectedCorrelationMagnitude
        (correlationProjection (stateAtScale scale)) left right
      ≤ amplitude * Power.rationalPower ratio (physicalDistance left right)

open QuantitativeCorrelationDecayTrajectory public

clusteringFromCorrelationTrajectoryAtScale :
  (trajectory : QuantitativeCorrelationDecayTrajectory) →
  Nat → R108.UniformGeometricConnectedClustering (Observable trajectory)
clusteringFromCorrelationTrajectoryAtScale trajectory scale = record
  { R108.UniformGeometricConnectedClustering.distance =
      physicalDistance trajectory
  ; R108.UniformGeometricConnectedClustering.connectedCovarianceMagnitude =
      connectedCorrelationMagnitude trajectory
        (correlationProjection trajectory (stateAtScale trajectory scale))
  ; R108.UniformGeometricConnectedClustering.amplitude = amplitude trajectory
  ; R108.UniformGeometricConnectedClustering.ratio = ratio trajectory
  ; R108.UniformGeometricConnectedClustering.amplitudeNonnegative =
      amplitudeNonnegative trajectory
  ; R108.UniformGeometricConnectedClustering.ratioNonnegative =
      ratioNonnegative trajectory
  ; R108.UniformGeometricConnectedClustering.ratioStrictlyBelowOne =
      ratioStrictlyBelowOne trajectory
  ; R108.UniformGeometricConnectedClustering.connectedCovarianceBound =
      geometricDecayAtEveryScale trajectory scale
  }

------------------------------------------------------------------------
-- Full unified-norm tactic.  It is deliberately stronger than the B-facing
-- trajectory above, and only ADAPTS to it.
------------------------------------------------------------------------

record PhysicalYMUnifiedPolymerNormProducer : Set₁ where
  field
    State OrdinaryObservable CompositeObservable WeightedCorrelation Bound : Set

    authority : UnifiedPolymerSchwingerNormAuthority
      State OrdinaryObservable CompositeObservable WeightedCorrelation Bound

    LargeFieldRegulatorControlled : State → Set
    FieldDerivativeSeminormsControlled : State → Set
    PolymerSizeDecayControlled : State → Set
    CompositeOperatorMixingControlled : State → Set

    stateAtScale : Nat → State

    physicalDistance : OrdinaryObservable → OrdinaryObservable → Nat
    connectedCorrelationMagnitude :
      WeightedCorrelation → OrdinaryObservable → OrdinaryObservable → ℚ

    separationAmplitude separationRatio : ℚ
    separationAmplitudeNonnegative : 0ℚ ≤ separationAmplitude
    separationRatioNonnegative : 0ℚ ≤ separationRatio
    separationRatioStrictlyBelowOne : separationRatio < 1ℚ

    physicalSeparationDecay : ∀ scale left right →
      connectedCorrelationMagnitude
        (UnifiedPolymerSchwingerNormAuthority.correlationProjection
          authority (stateAtScale scale)) left right
      ≤ separationAmplitude
        * Power.rationalPower separationRatio (physicalDistance left right)

    allNonSeparationCoordinatesControlled : ∀ scale →
      LargeFieldRegulatorControlled (stateAtScale scale)
      × FieldDerivativeSeminormsControlled (stateAtScale scale)
      × PolymerSizeDecayControlled (stateAtScale scale)
      × CompositeOperatorMixingControlled (stateAtScale scale)

    incrementControl : UnifiedRGIncrementControl authority

open PhysicalYMUnifiedPolymerNormProducer public

correlationDecayTrajectoryFromUnifiedProducer :
  PhysicalYMUnifiedPolymerNormProducer → QuantitativeCorrelationDecayTrajectory
correlationDecayTrajectoryFromUnifiedProducer producer = record
  { QuantitativeCorrelationDecayTrajectory.State = State producer
  ; QuantitativeCorrelationDecayTrajectory.Observable = OrdinaryObservable producer
  ; QuantitativeCorrelationDecayTrajectory.Correlation = WeightedCorrelation producer
  ; QuantitativeCorrelationDecayTrajectory.correlationProjection =
      UnifiedPolymerSchwingerNormAuthority.correlationProjection (authority producer)
  ; QuantitativeCorrelationDecayTrajectory.stateAtScale = stateAtScale producer
  ; QuantitativeCorrelationDecayTrajectory.physicalDistance = physicalDistance producer
  ; QuantitativeCorrelationDecayTrajectory.connectedCorrelationMagnitude =
      connectedCorrelationMagnitude producer
  ; QuantitativeCorrelationDecayTrajectory.amplitude = separationAmplitude producer
  ; QuantitativeCorrelationDecayTrajectory.ratio = separationRatio producer
  ; QuantitativeCorrelationDecayTrajectory.amplitudeNonnegative =
      separationAmplitudeNonnegative producer
  ; QuantitativeCorrelationDecayTrajectory.ratioNonnegative =
      separationRatioNonnegative producer
  ; QuantitativeCorrelationDecayTrajectory.ratioStrictlyBelowOne =
      separationRatioStrictlyBelowOne producer
  ; QuantitativeCorrelationDecayTrajectory.geometricDecayAtEveryScale =
      physicalSeparationDecay producer
  }

clusteringAtScale :
  (producer : PhysicalYMUnifiedPolymerNormProducer) →
  Nat → R108.UniformGeometricConnectedClustering (OrdinaryObservable producer)
clusteringAtScale producer =
  clusteringFromCorrelationTrajectoryAtScale
    (correlationDecayTrajectoryFromUnifiedProducer producer)

unifiedNormProjectionClosureLevel : ProofLevel
unifiedNormProjectionClosureLevel = machineChecked

quantitativeCorrelationProjectionToClusteringLevel : ProofLevel
quantitativeCorrelationProjectionToClusteringLevel = machineChecked

unifiedNormToCorrelationDecayTrajectoryLevel : ProofLevel
unifiedNormToCorrelationDecayTrajectoryLevel = machineChecked

brydgesDimockHurdNormPrecedentLevel : ProofLevel
brydgesDimockHurdNormPrecedentLevel = standardImported

brydgesMitterScoppolaNormPrecedentLevel : ProofLevel
brydgesMitterScoppolaNormPrecedentLevel = standardImported

polonyiSailerCompositeRGPrecedentLevel : ProofLevel
polonyiSailerCompositeRGPrecedentLevel = standardImported

-- Canonical B-facing physical theorem.  A proof may come from the unified norm,
-- a direct cluster expansion, a semigroup estimate, or any other valid route.
physicalYMCorrelationDecayTrajectoryLevel : ProofLevel
physicalYMCorrelationDecayTrajectoryLevel = conditional

-- Stronger optional tactic, retained because it simultaneously advances A/C.
physicalYMUnifiedPolymerNormProducerLevel : ProofLevel
physicalYMUnifiedPolymerNormProducerLevel = conditional
