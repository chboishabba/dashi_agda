module DASHI.Physics.YangMills.BalabanUnifiedPolymerSchwingerNormExact where

------------------------------------------------------------------------
-- ROUND65 HIGHEST-ALPHA CONTINUUM DEVICE:
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
-- DASHI CONTRIBUTION
--
-- The key mathematical design constraint is made exact: ordinary Schwinger
-- observables, renormalized composite insertions and separation-weighted
-- connected correlations are all required to be 1-Lipschitz projections of ONE
-- stronger same-family norm.  Therefore ONE RG increment/contraction estimate
-- automatically supplies the same Cauchy modulus to all three consumers.
--
-- This is the mechanism by which the seven-programme graph can potentially
-- collapse programmes P3--P6 into one strong continuum RG theorem without
-- proof-splicing unrelated limits.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)

open import DASHI.Physics.YangMills.CompactLieProofLevel

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
          (stateAtScale scale) (stateAtScale (Nat.suc scale)))
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
      (ordinaryProjection authority (stateAtScale control (Nat.suc scale))))
    (incrementMajorant control scale)
ordinaryIncrementBound {authority = authority} control scale =
  transitive authority
    (ordinaryProjectionNonexpansive authority
      (stateAtScale control scale)
      (stateAtScale control (Nat.suc scale)))
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
      (compositeProjection authority (stateAtScale control (Nat.suc scale))))
    (incrementMajorant control scale)
compositeIncrementBound {authority = authority} control scale =
  transitive authority
    (compositeProjectionNonexpansive authority
      (stateAtScale control scale)
      (stateAtScale control (Nat.suc scale)))
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
      (correlationProjection authority (stateAtScale control (Nat.suc scale))))
    (incrementMajorant control scale)
correlationIncrementBound {authority = authority} control scale =
  transitive authority
    (correlationProjectionNonexpansive authority
      (stateAtScale control scale)
      (stateAtScale control (Nat.suc scale)))
    (unifiedIncrementBound control scale)

------------------------------------------------------------------------
-- Physical content required of the actual Yang--Mills norm.
--
-- This is intentionally one producer.  Large-field regulation, field
-- derivatives/composite insertions, polymer-size decay and physical separation
-- decay are coordinates of the SAME norm rather than independent receipts.
------------------------------------------------------------------------

record PhysicalYMUnifiedPolymerNormProducer : Set₁ where
  field
    State OrdinaryObservable CompositeObservable WeightedCorrelation Bound : Set

    authority : UnifiedPolymerSchwingerNormAuthority
      State OrdinaryObservable CompositeObservable WeightedCorrelation Bound

    -- Source-native coordinates that the norm must dominate simultaneously.
    LargeFieldRegulatorControlled : State → Set
    FieldDerivativeSeminormsControlled : State → Set
    PolymerSizeDecayControlled : State → Set
    PhysicalSeparationDecayControlled : State → Set
    CompositeOperatorMixingControlled : State → Set

    stateAtScale : Nat → State

    allCoordinatesControlled : ∀ scale →
      LargeFieldRegulatorControlled (stateAtScale scale)
      × FieldDerivativeSeminormsControlled (stateAtScale scale)
      × PolymerSizeDecayControlled (stateAtScale scale)
      × PhysicalSeparationDecayControlled (stateAtScale scale)
      × CompositeOperatorMixingControlled (stateAtScale scale)

    incrementControl : UnifiedRGIncrementControl authority

open PhysicalYMUnifiedPolymerNormProducer public

unifiedNormProjectionClosureLevel : ProofLevel
unifiedNormProjectionClosureLevel = machineChecked

brydgesDimockHurdNormPrecedentLevel : ProofLevel
brydgesDimockHurdNormPrecedentLevel = standardImported

brydgesMitterScoppolaNormPrecedentLevel : ProofLevel
brydgesMitterScoppolaNormPrecedentLevel = standardImported

polonyiSailerCompositeRGPrecedentLevel : ProofLevel
polonyiSailerCompositeRGPrecedentLevel = standardImported

physicalYMUnifiedPolymerNormProducerLevel : ProofLevel
physicalYMUnifiedPolymerNormProducerLevel = conditional
