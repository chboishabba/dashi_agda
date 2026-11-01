module DASHI.Finance.TradingControlPermissionSeparationExact where

open import DASHI.Core.Prelude

import DASHI.Core.IntersectionalNonFactorability as NF
import DASHI.Trading.PermissionKernel as Legacy
import DASHI.Finance.TradingPermissionActionRefinementExact as Refine

------------------------------------------------------------------------
-- Correct the legacy semantic mixing.
--
-- ACT/HOLD/BAN is not a homogeneous control carrier:
-- ACT and HOLD are action/control notions, while BAN is modal prohibition.
-- We therefore split control intent from risk-increase permission.
------------------------------------------------------------------------

data ControlIntent : Set where
  reduceControl : ControlIntent
  holdControl : ControlIntent
  increaseControl : ControlIntent

data RiskIncreasePermission : Set where
  increasePermitted : RiskIncreasePermission
  increaseNotPermitted : RiskIncreasePermission

record TradingDecision : Set where
  constructor tradingDecision
  field
    control : ControlIntent
    riskIncreasePermission : RiskIncreasePermission

open TradingDecision public

------------------------------------------------------------------------
-- Legacy compatibility is a lossy adapter only.
------------------------------------------------------------------------

legacyPermissionSurface : TradingDecision → Legacy.Permission
legacyPermissionSurface (tradingDecision increaseControl increasePermitted) = Legacy.ACT
legacyPermissionSurface (tradingDecision holdControl increasePermitted) = Legacy.HOLD
legacyPermissionSurface (tradingDecision reduceControl increasePermitted) = Legacy.ACT
legacyPermissionSurface (tradingDecision increaseControl increaseNotPermitted) = Legacy.BAN
legacyPermissionSurface (tradingDecision holdControl increaseNotPermitted) = Legacy.BAN
legacyPermissionSurface (tradingDecision reduceControl increaseNotPermitted) = Legacy.BAN

------------------------------------------------------------------------
-- Exact witness: BAN collapses incompatible control intents.
------------------------------------------------------------------------

banIncreaseWorld : TradingDecision
banIncreaseWorld = tradingDecision increaseControl increaseNotPermitted

banHoldWorld : TradingDecision
banHoldWorld = tradingDecision holdControl increaseNotPermitted

banReduceWorld : TradingDecision
banReduceWorld = tradingDecision reduceControl increaseNotPermitted

banSurfaceCollisionIncreaseHold :
  legacyPermissionSurface banIncreaseWorld ≡ legacyPermissionSurface banHoldWorld
banSurfaceCollisionIncreaseHold = refl

banSurfaceCollisionHoldReduce :
  legacyPermissionSurface banHoldWorld ≡ legacyPermissionSurface banReduceWorld
banSurfaceCollisionHoldReduce = refl

controlDiffersIncreaseHold :
  control banIncreaseWorld ≡ control banHoldWorld → ⊥
controlDiffersIncreaseHold ()

legacyPermissionCannotRecoverControl :
  NF.NonFactorabilityWitness legacyPermissionSurface control
legacyPermissionCannotRecoverControl =
  NF.nonFactorabilityWitness
    banIncreaseWorld
    banHoldWorld
    banSurfaceCollisionIncreaseHold
    controlDiffersIncreaseHold

noLegacyPermissionOnlyControlCompiler :
  NF.FactorsThrough legacyPermissionSurface control → ⊥
noLegacyPermissionOnlyControlCompiler =
  NF.witnessRulesOutEveryFlatFactorisation
    legacyPermissionCannotRecoverControl

------------------------------------------------------------------------
-- State-aware control compilation.
--
-- Risk permission constrains which controls are admissible; it does not choose
-- the control. Exposure and objective/risk state choose among admissible
-- controls later.
------------------------------------------------------------------------

controlAllowed : RiskIncreasePermission → ControlIntent → Bool
controlAllowed increasePermitted reduceControl = true
controlAllowed increasePermitted holdControl = true
controlAllowed increasePermitted increaseControl = true
controlAllowed increaseNotPermitted reduceControl = true
controlAllowed increaseNotPermitted holdControl = true
controlAllowed increaseNotPermitted increaseControl = false

blockedIncreaseForbidden :
  controlAllowed increaseNotPermitted increaseControl ≡ false
blockedIncreaseForbidden = refl

blockedHoldAllowed :
  controlAllowed increaseNotPermitted holdControl ≡ true
blockedHoldAllowed = refl

blockedReduceAllowed :
  controlAllowed increaseNotPermitted reduceControl ≡ true
blockedReduceAllowed = refl

------------------------------------------------------------------------
-- Exposure-conditioned controller. This is where the apparent "ACT but don't
-- ACT" paradox disappears: prohibition is one coordinate, action is another.
------------------------------------------------------------------------

compileBlockedControl : Refine.ExposureState → ControlIntent
compileBlockedControl Refine.flatExposure = holdControl
compileBlockedControl Refine.longExposure = reduceControl
compileBlockedControl Refine.shortExposure = reduceControl

blockedFlatHolds :
  compileBlockedControl Refine.flatExposure ≡ holdControl
blockedFlatHolds = refl

blockedLongReduces :
  compileBlockedControl Refine.longExposure ≡ reduceControl
blockedLongReduces = refl

blockedShortReduces :
  compileBlockedControl Refine.shortExposure ≡ reduceControl
blockedShortReduces = refl

------------------------------------------------------------------------
-- Supersession boundary.
------------------------------------------------------------------------

record LegacyPermissionSupersessionBoundary : Set where
  constructor legacyPermissionSupersessionBoundary
  field
    actHoldBanHomogeneousControlCarrier : Bool
    actHoldBanHomogeneousControlCarrierIsFalse :
      actHoldBanHomogeneousControlCarrier ≡ false
    banIsConcreteAction : Bool
    banIsConcreteActionIsFalse : banIsConcreteAction ≡ false
    permissionAndControlMustBeSeparate : Bool
    permissionAndControlMustBeSeparateIsTrue :
      permissionAndControlMustBeSeparate ≡ true
    legacyCarrierRetainedOnlyAsCompatibilitySurface : Bool
    legacyCarrierRetainedOnlyAsCompatibilitySurfaceIsTrue :
      legacyCarrierRetainedOnlyAsCompatibilitySurface ≡ true

canonicalLegacyPermissionSupersessionBoundary :
  LegacyPermissionSupersessionBoundary
canonicalLegacyPermissionSupersessionBoundary =
  legacyPermissionSupersessionBoundary false refl false refl true refl true refl

boundaryStatement : String
boundaryStatement =
  "Legacy ACT/HOLD/BAN mixes action with prohibition. The corrected model uses an independent ternary control axis (reduce/hold/increase) and a separate risk-increase permission bit. BAN survives only as a lossy compatibility projection."
