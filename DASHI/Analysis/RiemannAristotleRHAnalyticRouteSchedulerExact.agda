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
-- Two zero-side route classes remain logically admissible, but the reconciled
-- finite-near audit now gives a structural prerequisite ordering: the direct
-- signed finite evaluation attacks the terminal finite value immediately,
-- whereas the explicit-formula fallback still requires uninhabited target
-- modulation/window and lawful extraction producers first. This is not an
-- invented theorem-difficulty score; it is dependency-graph dominance.
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
-- Logical admissibility remains proof-relevant.
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
-- Current structural precedence. The historical generic cost selector remains
-- below for compatibility, but must not be interpreted as permission to make a
-- dependency-dominated fallback outrank the direct route merely by declaring a
-- smaller arbitrary Nat cost.
------------------------------------------------------------------------

data CurrentHighestAlphaRoute : RHAnalyticExperiment → Set where
  directOffRouteHighestAlpha :
    CurrentHighestAlphaRoute directPoleNearEvaluation
  gammaRouteHighestAlpha :
    CurrentHighestAlphaRoute repairGammaPrecision

explicitFormulaFallbackNotCurrentHighestAlpha :
  CurrentHighestAlphaRoute buildPoleNearExplicitFormulaBridge → ⊥
explicitFormulaFallbackNotCurrentHighestAlpha ()

directAuditPrecedencePin :
  Route.directRouteIsCurrentHighestAlphaZeroSideRoute ≡ true
directAuditPrecedencePin =
  Route.directRouteIsCurrentHighestAlphaZeroSideRouteIsTrue

explicitFormulaStillLogicallyAdmissible :
  RHAnalyticSchedulable buildPoleNearExplicitFormulaBridge
explicitFormulaStillLogicallyAdmissible = explicitFormulaBridgeIsSchedulable

------------------------------------------------------------------------
-- Historical cost/order only after RH admissibility. This interface is retained
-- for compatibility; current highest-alpha selection additionally respects the
-- structural precedence above.
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

record SelectedCurrentHighestAlphaExperiment
    (surface : RHAnalyticCostSurface) : Set₁ where
  constructor selected-current-highest-alpha-experiment
  field
    historicalSelection : SelectedRHAnalyticExperiment surface
    respectsCurrentStructuralPrecedence :
      CurrentHighestAlphaRoute (SelectedRHAnalyticExperiment.selected historicalSelection)

open SelectedCurrentHighestAlphaExperiment public

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

currentDirectRouteStructurallyPrecedesExplicitFormulaFallback : Bool
currentDirectRouteStructurallyPrecedesExplicitFormulaFallback = true

currentDirectRouteStructurallyPrecedesExplicitFormulaFallbackIsTrue :
  currentDirectRouteStructurallyPrecedesExplicitFormulaFallback ≡ true
currentDirectRouteStructurallyPrecedesExplicitFormulaFallbackIsTrue = refl
