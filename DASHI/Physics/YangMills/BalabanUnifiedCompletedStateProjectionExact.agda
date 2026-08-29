module DASHI.Physics.YangMills.BalabanUnifiedCompletedStateProjectionExact where

------------------------------------------------------------------------
-- ROUND73: ONE COMPLETED UNIFIED RG STATE -> ONE SAME-FAMILY LIMIT
--
-- This file removes another potential proof-splicing point from continuum
-- completion.  Once the physical RG trajectory converges in ONE complete
-- unified state space, ordinary Schwinger observables, composite insertions and
-- separation-weighted connected correlations do not get independently chosen
-- limits: continuity of their already-nonexpansive projections forces all three
-- to be projections of the SAME completed state.
--
-- The analytic existence of that completed state (tightness/completeness in the
-- physical distribution/measure topology) remains a physical theorem.  This
-- module proves the no-splicing consequence once that one convergence exists.
--
-- CALIBRATION
-- David C. Brydges, John Dimock and Thomas R. Hurd,
-- "Estimates on Renormalization Group Transformations",
-- Canadian Journal of Mathematics 50 (1998), 756--793.
-- DOI: 10.4153/CJM-1998-041-5.
--
-- P. K. Mitter, "The Exact Renormalization Group",
-- Encyclopedia of Mathematical Physics (2006).
-- DOI: 10.1016/B0-12-512666-2/00071-7.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanUnifiedPolymerSchwingerNormExact as Unified

record UnifiedCompletedStateAuthority
    (State Ordinary Composite Correlation Bound : Set) : Set₁ where
  field
    normAuthority : Unified.UnifiedPolymerSchwingerNormAuthority
      State Ordinary Composite Correlation Bound

    stateAtScale : Nat → State
    limitState : State

    StateConverges : (Nat → State) → State → Set
    OrdinaryConverges : (Nat → Ordinary) → Ordinary → Set
    CompositeConverges : (Nat → Composite) → Composite → Set
    CorrelationConverges : (Nat → Correlation) → Correlation → Set

    unifiedStateConverges : StateConverges stateAtScale limitState

    -- Nonexpansiveness in the unified norm is already stored in normAuthority.
    -- These three fields are only the standard topological consequence that a
    -- nonexpansive map is continuous in the chosen convergence structure.
    ordinaryProjectionContinuous :
      StateConverges stateAtScale limitState →
      OrdinaryConverges
        (λ scale → Unified.ordinaryProjection normAuthority (stateAtScale scale))
        (Unified.ordinaryProjection normAuthority limitState)

    compositeProjectionContinuous :
      StateConverges stateAtScale limitState →
      CompositeConverges
        (λ scale → Unified.compositeProjection normAuthority (stateAtScale scale))
        (Unified.compositeProjection normAuthority limitState)

    correlationProjectionContinuous :
      StateConverges stateAtScale limitState →
      CorrelationConverges
        (λ scale → Unified.correlationProjection normAuthority (stateAtScale scale))
        (Unified.correlationProjection normAuthority limitState)

open UnifiedCompletedStateAuthority public

record SameUnifiedContinuumFamily
    {State Ordinary Composite Correlation Bound : Set}
    (dataSet : UnifiedCompletedStateAuthority
      State Ordinary Composite Correlation Bound) : Set₁ where
  field
    completedState : State
    ordinaryLimit : Ordinary
    compositeLimit : Composite
    correlationLimit : Correlation

    completedStateIsLiteralLimit : completedState ≡ limitState dataSet

    ordinaryIsProjection :
      ordinaryLimit ≡
      Unified.ordinaryProjection (normAuthority dataSet) completedState

    compositeIsProjection :
      compositeLimit ≡
      Unified.compositeProjection (normAuthority dataSet) completedState

    correlationIsProjection :
      correlationLimit ≡
      Unified.correlationProjection (normAuthority dataSet) completedState

    ordinaryConvergence :
      OrdinaryConverges dataSet
        (λ scale → Unified.ordinaryProjection
          (normAuthority dataSet) (stateAtScale dataSet scale))
        ordinaryLimit

    compositeConvergence :
      CompositeConverges dataSet
        (λ scale → Unified.compositeProjection
          (normAuthority dataSet) (stateAtScale dataSet scale))
        compositeLimit

    correlationConvergence :
      CorrelationConverges dataSet
        (λ scale → Unified.correlationProjection
          (normAuthority dataSet) (stateAtScale dataSet scale))
        correlationLimit

open SameUnifiedContinuumFamily public

sameUnifiedContinuumFamily :
  ∀ {State Ordinary Composite Correlation Bound}
    (dataSet : UnifiedCompletedStateAuthority
      State Ordinary Composite Correlation Bound) →
  SameUnifiedContinuumFamily dataSet
sameUnifiedContinuumFamily dataSet = record
  { completedState = limitState dataSet
  ; ordinaryLimit = Unified.ordinaryProjection
      (normAuthority dataSet) (limitState dataSet)
  ; compositeLimit = Unified.compositeProjection
      (normAuthority dataSet) (limitState dataSet)
  ; correlationLimit = Unified.correlationProjection
      (normAuthority dataSet) (limitState dataSet)
  ; completedStateIsLiteralLimit = refl
  ; ordinaryIsProjection = refl
  ; compositeIsProjection = refl
  ; correlationIsProjection = refl
  ; ordinaryConvergence = ordinaryProjectionContinuous dataSet
      (unifiedStateConverges dataSet)
  ; compositeConvergence = compositeProjectionContinuous dataSet
      (unifiedStateConverges dataSet)
  ; correlationConvergence = correlationProjectionContinuous dataSet
      (unifiedStateConverges dataSet)
  }

unifiedCompletedStateProjectionLevel : ProofLevel
unifiedCompletedStateProjectionLevel = machineChecked

-- Physical continuum seam after this theorem: construct ONE complete/topological
-- state limit from the cutoff-uniform unified RG bounds, and identify its
-- ordinary projection with the Schwinger family of the limiting measure.  No
-- separate choices of composite/correlation subsequences are permitted or
-- needed after that state-level convergence is established.
physicalUnifiedCompletedStateExistenceLevel : ProofLevel
physicalUnifiedCompletedStateExistenceLevel = conditional

physicalCompletedStateMeasureSchwingerIdentificationLevel : ProofLevel
physicalCompletedStateMeasureSchwingerIdentificationLevel = conditional
