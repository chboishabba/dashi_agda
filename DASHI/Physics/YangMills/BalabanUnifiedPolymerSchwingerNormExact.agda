module DASHI.Physics.YangMills.BalabanUnifiedPolymerSchwingerNormExact where

------------------------------------------------------------------------
-- ROUND65/R271 HIGHEST-ALPHA CONTINUUM DEVICE:
-- ONE POLYMER/SCHWINGER NORM, THREE DOWNSTREAM PROJECTIONS
--
-- PRIMARY SOURCES / CALIBRATION
--
-- David C. Brydges, John Dimock and Thomas R. Hurd,
-- "Estimates on Renormalization Group Transformations",
-- Canadian Journal of Mathematics 50 (1998), 756--793.
-- DOI: 10.4153/CJM-1998-041-5.
--
-- David C. Brydges, P. K. Mitter and B. Scoppola,
-- "Critical (Phi^4)_{3,epsilon}", Communications in Mathematical Physics
-- 240 (2003), 281--327. DOI: 10.1007/s00220-003-0895-4.
--
-- P. K. Mitter,
-- "The Exact Renormalization Group", Encyclopedia of Mathematical Physics
-- (2006). DOI: 10.1016/B0-12-512666-2/00071-7.
--
-- Janos Polonyi and Kornel Sailer,
-- "Renormalization of Composite Operators", Physical Review D 63 (2001),
-- 105006. DOI: 10.1103/PhysRevD.63.105006.
--
-- Tadeusz Balaban, John Imbrie and Arthur Jaffe,
-- "Exact Renormalization Group for Gauge Theories", in Progress in Gauge
-- Field Theory (1984), pp. 79--103.
-- DOI: 10.1007/978-1-4757-0280-4_4.
--
-- AUTHORITY BOUNDARY
--
-- These sources motivate polymer activities, large-field regulators, field
-- derivative seminorms, decay weights and RG transport of composite operators.
-- They do not by citation prove the nonperturbative four-dimensional pure
-- Yang--Mills estimate below.
--
-- R271 CORRECTION
--
-- The old producer stored `PhysicalSeparationDecayControlled : State -> Set`.
-- That was too opaque to pay the actual mass-gap consumer: it named a property
-- without exposing the connected correlation, physical distance, amplitude,
-- ratio, or quantitative decay inequality.
--
-- The producer now carries a literal rational interpretation of its SAME
-- `correlationProjection` and a geometric bound
--
--   |Cov_s(F,G)| <= A q^(d(F,G)),   0 <= q < 1,
--
-- at every RG scale.  This compiles directly to the existing
-- `UniformGeometricConnectedClustering` carrier.  Thus the unified-norm route
-- can no longer claim "physical separation controlled" without actually
-- producing the canonical clustering-shaped theorem.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; suc)
open import Data.Product using (_×_)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; 1ℚ; _*_; _≤_; _<_)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanFiniteInfluenceRowMassPowerExact as Power
import DASHI.Physics.YangMills.BalabanRowCPostBC2PhysicalCompletionRound108Exact as R108

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
-- Physical content required of the actual Yang--Mills norm.
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

    -- R271 quantitative replacement for the old opaque separation predicate.
    physicalDistance : OrdinaryObservable → OrdinaryObservable → Nat
    connectedCorrelationMagnitude :
      WeightedCorrelation → OrdinaryObservable → OrdinaryObservable → ℚ

    separationAmplitude separationRatio : ℚ
    separationAmplitudeNonnegative : 0ℚ ≤ separationAmplitude
    separationRatioNonnegative : 0ℚ ≤ separationRatio
    separationRatioStrictlyBelowOne : separationRatio < 1ℚ

    physicalSeparationDecay : ∀ scale left right →
      connectedCorrelationMagnitude
        (correlationProjection authority (stateAtScale scale)) left right
      ≤ separationAmplitude
        * Power.rationalPower separationRatio (physicalDistance left right)

    allNonSeparationCoordinatesControlled : ∀ scale →
      LargeFieldRegulatorControlled (stateAtScale scale)
      × FieldDerivativeSeminormsControlled (stateAtScale scale)
      × PolymerSizeDecayControlled (stateAtScale scale)
      × CompositeOperatorMixingControlled (stateAtScale scale)

    incrementControl : UnifiedRGIncrementControl authority

open PhysicalYMUnifiedPolymerNormProducer public

------------------------------------------------------------------------
-- Direct clustering compiler from the SAME correlation projection.
------------------------------------------------------------------------

clusteringAtScale :
  (producer : PhysicalYMUnifiedPolymerNormProducer) →
  Nat →
  R108.UniformGeometricConnectedClustering (OrdinaryObservable producer)
clusteringAtScale producer scale = record
  { R108.UniformGeometricConnectedClustering.distance =
      physicalDistance producer
  ; R108.UniformGeometricConnectedClustering.connectedCovarianceMagnitude =
      connectedCorrelationMagnitude producer
        (correlationProjection
          (authority producer) (stateAtScale producer scale))
  ; R108.UniformGeometricConnectedClustering.amplitude =
      separationAmplitude producer
  ; R108.UniformGeometricConnectedClustering.ratio =
      separationRatio producer
  ; R108.UniformGeometricConnectedClustering.amplitudeNonnegative =
      separationAmplitudeNonnegative producer
  ; R108.UniformGeometricConnectedClustering.ratioNonnegative =
      separationRatioNonnegative producer
  ; R108.UniformGeometricConnectedClustering.ratioStrictlyBelowOne =
      separationRatioStrictlyBelowOne producer
  ; R108.UniformGeometricConnectedClustering.connectedCovarianceBound =
      physicalSeparationDecay producer scale
  }

unifiedNormProjectionClosureLevel : ProofLevel
unifiedNormProjectionClosureLevel = machineChecked

quantitativeCorrelationProjectionToClusteringLevel : ProofLevel
quantitativeCorrelationProjectionToClusteringLevel = machineChecked

brydgesDimockHurdNormPrecedentLevel : ProofLevel
brydgesDimockHurdNormPrecedentLevel = standardImported

brydgesMitterScoppolaNormPrecedentLevel : ProofLevel
brydgesMitterScoppolaNormPrecedentLevel = standardImported

polonyiSailerCompositeRGPrecedentLevel : ProofLevel
polonyiSailerCompositeRGPrecedentLevel = standardImported

-- The physical theorem is now falsifiable at the canonical clustering surface:
-- an inhabitant must expose the actual connected correlation and prove the
-- uniform geometric inequality, not merely inhabit an opaque Set.
physicalYMUnifiedPolymerNormProducerLevel : ProofLevel
physicalYMUnifiedPolymerNormProducerLevel = conditional
