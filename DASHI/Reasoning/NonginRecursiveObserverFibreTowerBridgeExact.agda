module DASHI.Reasoning.NonginRecursiveObserverFibreTowerBridgeExact where

------------------------------------------------------------------------
-- NONGIN OBSERVER DEPTH <-> GENERIC RECURSIVE FIBRE TOWER
--
-- The Nongin observer-depth owner already supplies a Nat-indexed carrier and
-- one-step truncation.  DASHI.Cognition.RecursiveFibreTower independently owns
-- the generic inverse-system interface.  This file welds the two literally:
--
--   Level n = ObserverDepthState Observer X n
--   project = truncateOne
--
-- An infinite observer stream then determines a coherent inverse-limit point.
-- This is a structural inverse-system theorem only: no convergence metric,
-- p-adic psychological valuation, completeness theorem, or empirical observer
-- semantics is inferred.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import DASHI.Core.Prelude using (⊥)

import DASHI.Cognition.RecursiveFibreTower as Fibre
import DASHI.Philosophy.NonginOriginFormalizationExact as Origin
import DASHI.Reasoning.NonginRecursiveObserverDepthTowerExact as Depth

observerDepthFibreTower :
  {Observer X : Set} →
  Fibre.FibreTower
observerDepthFibreTower {Observer} {X} = record
  { Fibre.Level = Depth.ObserverDepthState Observer X
  ; Fibre.project = λ level → Depth.truncateOne
  }

observerDepthProjectIsTruncateOne :
  {Observer X : Set}
  {level : Nat}
  (state : Depth.ObserverDepthState Observer X (suc level)) →
  Fibre.project (observerDepthFibreTower {Observer} {X}) level state
  ≡ Depth.truncateOne state
observerDepthProjectIsTruncateOne state = refl

------------------------------------------------------------------------
-- A supplied infinite observer stream canonically gives a coherent tower
-- point.  The level-n state retains precisely the first n supplied observers.
------------------------------------------------------------------------

streamStateAt :
  {Observer X : Set} →
  (observerAt : Nat → Observer) →
  X →
  (level : Nat) →
  Depth.ObserverDepthState Observer X level
streamStateAt observerAt x zero =
  Depth.depthZero x
streamStateAt observerAt x (suc level) =
  Depth.depthStep
    (observerAt level)
    (streamStateAt observerAt x level)

streamStateCoherent :
  {Observer X : Set}
  (observerAt : Nat → Observer)
  (x : X)
  (level : Nat) →
  Fibre.project
    (observerDepthFibreTower {Observer} {X})
    level
    (streamStateAt observerAt x (suc level))
  ≡ streamStateAt observerAt x level
streamStateCoherent observerAt x level = refl

observerStreamInverseLimit :
  {Observer X : Set} →
  (observerAt : Nat → Observer) →
  X →
  Fibre.InverseLimitPoint
    (observerDepthFibreTower {Observer} {X})
observerStreamInverseLimit observerAt x = record
  { Fibre.stateAt = streamStateAt observerAt x
  ; Fibre.coherent = streamStateCoherent observerAt x
  }

------------------------------------------------------------------------
-- The historical finite syntax commutes with the tower projection.
------------------------------------------------------------------------

historicalObserveStepProjects :
  {Observer X : Set}
  (observer : Observer)
  (term : Origin.ObserverTerm Observer X) →
  Fibre.project
    (observerDepthFibreTower {Observer} {X})
    (Depth.observerTermDepth term)
    (Depth.observerTermToDepthState
      (Origin.observes observer term))
  ≡ Depth.observerTermToDepthState term
historicalObserveStepProjects observer term = refl

historicalObservedIsTowerBase :
  {Observer X : Set}
  (x : X) →
  Depth.observerTermToDepthState
    (Origin.observed {Observer = Observer} x)
  ≡ Depth.depthZero x
historicalObservedIsTowerBase x = refl

------------------------------------------------------------------------
-- Promotion firewall.
------------------------------------------------------------------------

data FibreTowerBridgeImpliesPAdicPsychologicalMetric : Set where
data FibreTowerBridgeImpliesMetricConvergence : Set where

towerBridgeDoesNotCreatePAdicMetric :
  FibreTowerBridgeImpliesPAdicPsychologicalMetric →
  ⊥
towerBridgeDoesNotCreatePAdicMetric ()

towerBridgeDoesNotCreateMetricConvergence :
  FibreTowerBridgeImpliesMetricConvergence →
  ⊥
towerBridgeDoesNotCreateMetricConvergence ()

record NonginRecursiveObserverFibreTowerBridgeBoundary : Set where
  constructor nongin-recursive-observer-fibre-tower-bridge-boundary
  field
    fibreTowerAdapterPaid : Bool
    inverseLimitFromObserverStreamPaid : Bool
    historicalSyntaxProjectionCommutes : Bool
    pAdicMetricPromoted : Bool
    metricConvergencePromoted : Bool

open NonginRecursiveObserverFibreTowerBridgeBoundary public

canonicalNonginRecursiveObserverFibreTowerBridgeBoundary :
  NonginRecursiveObserverFibreTowerBridgeBoundary
canonicalNonginRecursiveObserverFibreTowerBridgeBoundary =
  nongin-recursive-observer-fibre-tower-bridge-boundary
    true true true false false
