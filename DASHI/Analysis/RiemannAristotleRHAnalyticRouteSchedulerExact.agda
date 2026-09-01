module DASHI.Analysis.RiemannAristotleRHAnalyticRouteSchedulerExact where

------------------------------------------------------------------------
-- RH ANALYTIC ROUTE-LEVEL BIDI SCHEDULER
--
-- This is the recursive child scheduler beneath the active high-ordinate queue.
-- It exposes only experiments whose outputs can feed one of the two live RH
-- analytic producers:
--
--   H_off^pole finite-near evaluation
--   H_Gamma precision repair.
--
-- The finite-near node has two currently admissible route families:
--   direct signed finite evaluation;
--   construct a literal target-centred explicit-formula bridge.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Analysis.RiemannAristotlePoleQuotientFiniteNearRouteAuditExact as Route

------------------------------------------------------------------------
-- Route-level RH experiments.
------------------------------------------------------------------------

data RHAnalyticExperiment : Set where
  directPoleNearEvaluation
  buildPoleNearExplicitFormulaBridge
  repairGammaPrecision
  reuseHermitianG3AsIfSameCarrier
  complexPoissonWithoutCarrierBridge
  countZerosOnly
  absoluteMajorizeNearSum
  namedHardySearchWithoutBridge
  : RHAnalyticExperiment

data RHAnalyticProducer : Set where
  finiteNearProducer
  gammaPrecisionProducer
  : RHAnalyticProducer

experimentFeeds : RHAnalyticExperiment → RHAnalyticProducer
experimentFeeds directPoleNearEvaluation = finiteNearProducer
experimentFeeds buildPoleNearExplicitFormulaBridge = finiteNearProducer
experimentFeeds repairGammaPrecision = gammaPrecisionProducer
experimentFeeds reuseHermitianG3AsIfSameCarrier = finiteNearProducer
experimentFeeds complexPoissonWithoutCarrierBridge = finiteNearProducer
experimentFeeds countZerosOnly = finiteNearProducer
experimentFeeds absoluteMajorizeNearSum = finiteNearProducer
experimentFeeds namedHardySearchWithoutBridge = finiteNearProducer

------------------------------------------------------------------------
-- Admissibility is proof-relevant, not a label or score.
------------------------------------------------------------------------

data RHAnalyticSchedulable : RHAnalyticExperiment → Set where
  directPoleNearIsSchedulable :
    RHAnalyticSchedulable directPoleNearEvaluation
  explicitFormulaBridgeIsSchedulable :
    RHAnalyticSchedulable buildPoleNearExplicitFormulaBridge
  gammaRepairIsSchedulable :
    RHAnalyticSchedulable repairGammaPrecision

wrongCarrierG3NotSchedulable :
  RHAnalyticSchedulable reuseHermitianG3AsIfSameCarrier → ⊥
wrongCarrierG3NotSchedulable ()

unbridgedComplexPoissonNotSchedulable :
  RHAnalyticSchedulable complexPoissonWithoutCarrierBridge → ⊥
unbridgedComplexPoissonNotSchedulable ()

countOnlyNotSchedulable :
  RHAnalyticSchedulable countZerosOnly → ⊥
countOnlyNotSchedulable ()

absoluteMajorantNotSchedulable :
  RHAnalyticSchedulable absoluteMajorizeNearSum → ⊥
absoluteMajorantNotSchedulable ()

nameOnlyHardyNotSchedulable :
  RHAnalyticSchedulable namedHardySearchWithoutBridge → ⊥
nameOnlyHardyNotSchedulable ()

------------------------------------------------------------------------
-- Exact link to the finite-near route audit.
------------------------------------------------------------------------

directRouteFeedsFiniteNear :
  Route.FeedsFiniteNearProducer Route.directlyEvaluatePoleNearSum
directRouteFeedsFiniteNear = Route.directRouteFeeds

explicitFormulaBridgeRouteFeedsFiniteNear :
  Route.FeedsFiniteNearProducer Route.constructLiteralPoleNearExplicitFormulaBridge
explicitFormulaBridgeRouteFeedsFiniteNear = Route.explicitFormulaBridgeFeeds

wrongCarrierHermitianRouteDoesNotFeedFiniteNear :
  Route.FeedsFiniteNearProducer Route.reuseHermitianG3WithoutBridge → ⊥
wrongCarrierHermitianRouteDoesNotFeedFiniteNear =
  Route.reuseHermitianG3WithoutBridgeDoesNotFeed

------------------------------------------------------------------------
-- Cost/order only after RH admissibility.
------------------------------------------------------------------------

record RHAnalyticCostSurface : Set₁ where
  constructor rh-analytic-cost-surface
  field
    cost : RHAnalyticExperiment → Nat
    Declared : RHAnalyticExperiment → Set
    costReference : String

open RHAnalyticCostSurface public

record SelectedRHAnalyticExperiment (surface : RHAnalyticCostSurface) : Set₁ where
  constructor selected-rh-analytic-experiment
  field
    selected : RHAnalyticExperiment
    selectedDeclared : Declared surface selected
    selectedSchedulable : RHAnalyticSchedulable selected
    minimalAmongDeclaredSchedulable :
      (alternative : RHAnalyticExperiment) →
      Declared surface alternative →
      RHAnalyticSchedulable alternative →
      cost surface selected ≤ cost surface alternative
    selectionReference : String

open SelectedRHAnalyticExperiment public

------------------------------------------------------------------------
-- Boundary.
------------------------------------------------------------------------

record RHAnalyticRouteSchedulerBoundary : Set where
  constructor rh-analytic-route-scheduler-boundary
  field
    directFinitePoleNearRouteActive : Bool
    directFinitePoleNearRouteActiveIsTrue : directFinitePoleNearRouteActive ≡ true

    literalExplicitFormulaBridgeRouteActive : Bool
    literalExplicitFormulaBridgeRouteActiveIsTrue :
      literalExplicitFormulaBridgeRouteActive ≡ true

    gammaPrecisionRepairRouteActive : Bool
    gammaPrecisionRepairRouteActiveIsTrue : gammaPrecisionRepairRouteActive ≡ true

    wrongCarrierHermitianReuseActive : Bool
    wrongCarrierHermitianReuseActiveIsFalse : wrongCarrierHermitianReuseActive ≡ false

    countOnlyRouteActive : Bool
    countOnlyRouteActiveIsFalse : countOnlyRouteActive ≡ false

    absoluteMajorantRouteActive : Bool
    absoluteMajorantRouteActiveIsFalse : absoluteMajorantRouteActive ≡ false

    nameOnlyHardyRouteActive : Bool
    nameOnlyHardyRouteActiveIsFalse : nameOnlyHardyRouteActive ≡ false

    theoremDifficultyOrderingInvented : Bool
    theoremDifficultyOrderingInventedIsFalse : theoremDifficultyOrderingInvented ≡ false

    rhDerived : Bool
    rhDerivedIsFalse : rhDerived ≡ false

canonicalRHAnalyticRouteSchedulerBoundary : RHAnalyticRouteSchedulerBoundary
canonicalRHAnalyticRouteSchedulerBoundary =
  rh-analytic-route-scheduler-boundary
    true refl
    true refl
    true refl
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
