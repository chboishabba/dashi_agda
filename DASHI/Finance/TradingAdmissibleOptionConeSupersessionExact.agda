module DASHI.Finance.TradingAdmissibleOptionConeSupersessionExact where

open import DASHI.Core.Prelude

import DASHI.Core.TypedDependencyCore as Dependency
import DASHI.Trading.PermissionKernel as Legacy

------------------------------------------------------------------------
-- Canonical trading control is a state-indexed admissible option cone.
--
-- No separate permission coordinate is paired with an action.  An action is
-- either admissible in the current state (because its precondition is
-- inhabited) or it is not.  This avoids tautological states such as
-- (reduce, not-permitted).
------------------------------------------------------------------------

data Exposure : Set where
  shortExposure flatExposure longExposure : Exposure

data RiskRegime : Set where
  riskClear riskCaution riskBlocked : RiskRegime

data ControlAction : Set where
  reduceAction holdAction increaseAction : ControlAction

record TradeState : Set where
  constructor tradeState
  field
    exposure : Exposure
    riskRegime : RiskRegime

open TradeState public

------------------------------------------------------------------------
-- Proof-relevant action preconditions.
------------------------------------------------------------------------

data TradePrecondition : TradeState → ControlAction → Set where
  holdAvailable :
    {state : TradeState} →
    TradePrecondition state holdAction

  reduceLong :
    {risk : RiskRegime} →
    TradePrecondition (tradeState longExposure risk) reduceAction

  reduceShort :
    {risk : RiskRegime} →
    TradePrecondition (tradeState shortExposure risk) reduceAction

  increaseFlatClear :
    TradePrecondition (tradeState flatExposure riskClear) increaseAction

  increaseLongClear :
    TradePrecondition (tradeState longExposure riskClear) increaseAction

  increaseShortClear :
    TradePrecondition (tradeState shortExposure riskClear) increaseAction

  increaseFlatCaution :
    TradePrecondition (tradeState flatExposure riskCaution) increaseAction

------------------------------------------------------------------------
-- Minimal post-state semantics for the control layer.  The execution layer can
-- later refine size, side, fills and costs without changing admissibility.
------------------------------------------------------------------------

data TradePostcondition :
    TradeState → ControlAction → TradeState → Set where
  holdPost :
    {state : TradeState} →
    TradePostcondition state holdAction state

  reduceLongPost :
    {risk : RiskRegime} →
    TradePostcondition
      (tradeState longExposure risk)
      reduceAction
      (tradeState flatExposure risk)

  reduceShortPost :
    {risk : RiskRegime} →
    TradePostcondition
      (tradeState shortExposure risk)
      reduceAction
      (tradeState flatExposure risk)

  increaseFlatPost :
    {risk : RiskRegime} →
    TradePostcondition
      (tradeState flatExposure risk)
      increaseAction
      (tradeState longExposure risk)

  increaseLongPost :
    TradePostcondition
      (tradeState longExposure riskClear)
      increaseAction
      (tradeState longExposure riskClear)

  increaseShortPost :
    TradePostcondition
      (tradeState shortExposure riskClear)
      increaseAction
      (tradeState shortExposure riskClear)

tradeActionSystem :
  Dependency.DependentActionSystem TradeState ControlAction
tradeActionSystem = record
  { Precondition = TradePrecondition
  ; Postcondition = TradePostcondition
  ; actionLabel = actionLabelLocal
  }
  where
    actionLabelLocal : ControlAction → String
    actionLabelLocal reduceAction = "reduce"
    actionLabelLocal holdAction = "hold"
    actionLabelLocal increaseAction = "increase"

------------------------------------------------------------------------
-- Canonical option cones.
------------------------------------------------------------------------

blockedFlat : TradeState
blockedFlat = tradeState flatExposure riskBlocked

blockedLong : TradeState
blockedLong = tradeState longExposure riskBlocked

blockedShort : TradeState
blockedShort = tradeState shortExposure riskBlocked

blockedFlatHold : TradePrecondition blockedFlat holdAction
blockedFlatHold = holdAvailable

blockedLongHold : TradePrecondition blockedLong holdAction
blockedLongHold = holdAvailable

blockedLongReduce : TradePrecondition blockedLong reduceAction
blockedLongReduce = reduceLong

blockedShortHold : TradePrecondition blockedShort holdAction
blockedShortHold = holdAvailable

blockedShortReduce : TradePrecondition blockedShort reduceAction
blockedShortReduce = reduceShort

blockedFlatCannotIncrease : TradePrecondition blockedFlat increaseAction → ⊥
blockedFlatCannotIncrease ()

blockedLongCannotIncrease : TradePrecondition blockedLong increaseAction → ⊥
blockedLongCannotIncrease ()

blockedShortCannotIncrease : TradePrecondition blockedShort increaseAction → ⊥
blockedShortCannotIncrease ()

blockedFlatCannotReduce : TradePrecondition blockedFlat reduceAction → ⊥
blockedFlatCannotReduce ()

------------------------------------------------------------------------
-- The key state is blocked + already exposed:
--
--   A(blocked,long) = {reduce, hold}
--
-- There is no truthful ACT/HOLD/BAN label for this cone.  It is not ACT in the
-- legacy sense because increase is unavailable; it is not HOLD because reduce
-- is available; and calling it BAN would falsely suggest action prohibition.
------------------------------------------------------------------------

data CanonicalConeShape : Set where
  holdOnlyCone reduceOrHoldCone increaseCapableCone : CanonicalConeShape

coneShape : TradeState → CanonicalConeShape
coneShape (tradeState flatExposure riskBlocked) = holdOnlyCone
coneShape (tradeState longExposure riskBlocked) = reduceOrHoldCone
coneShape (tradeState shortExposure riskBlocked) = reduceOrHoldCone
coneShape (tradeState exposure riskClear) = increaseCapableCone
coneShape (tradeState flatExposure riskCaution) = increaseCapableCone
coneShape (tradeState longExposure riskCaution) = reduceOrHoldCone
coneShape (tradeState shortExposure riskCaution) = reduceOrHoldCone

blockedLongConeShape : coneShape blockedLong ≡ reduceOrHoldCone
blockedLongConeShape = refl

blockedFlatConeShape : coneShape blockedFlat ≡ holdOnlyCone
blockedFlatConeShape = refl

------------------------------------------------------------------------
-- Legacy projection is necessarily lossy/incomplete.
------------------------------------------------------------------------

data LegacyProjectionResult : Set where
  legacyACT legacyHOLD legacyUnrepresentable : LegacyProjectionResult

projectConeToLegacy : CanonicalConeShape → LegacyProjectionResult
projectConeToLegacy increaseCapableCone = legacyACT
projectConeToLegacy holdOnlyCone = legacyHOLD
projectConeToLegacy reduceOrHoldCone = legacyUnrepresentable

blockedLongHasNoFaithfulLegacyPermission :
  projectConeToLegacy (coneShape blockedLong) ≡ legacyUnrepresentable
blockedLongHasNoFaithfulLegacyPermission = refl

blockedShortHasNoFaithfulLegacyPermission :
  projectConeToLegacy (coneShape blockedShort) ≡ legacyUnrepresentable
blockedShortHasNoFaithfulLegacyPermission = refl

------------------------------------------------------------------------
-- Historical BAN can therefore only be treated as a coarse alarm/status from
-- the old kernel.  It is not a member of the canonical action carrier and does
-- not determine the option cone.
------------------------------------------------------------------------

record LegacyBANBoundary : Set where
  constructor legacyBANBoundary
  field
    banIsCanonicalAction : Bool
    banIsCanonicalActionIsFalse : banIsCanonicalAction ≡ false

    banIsCanonicalPermissionCoordinate : Bool
    banIsCanonicalPermissionCoordinateIsFalse :
      banIsCanonicalPermissionCoordinate ≡ false

    blockedExposedConeRepresentableByActHoldBan : Bool
    blockedExposedConeRepresentableByActHoldBanIsFalse :
      blockedExposedConeRepresentableByActHoldBan ≡ false

    canonicalObjectIsStateIndexedAdmissibleActionSet : Bool
    canonicalObjectIsStateIndexedAdmissibleActionSetIsTrue :
      canonicalObjectIsStateIndexedAdmissibleActionSet ≡ true

canonicalLegacyBANBoundary : LegacyBANBoundary
canonicalLegacyBANBoundary =
  legacyBANBoundary false refl false refl false refl true refl

boundaryStatement : String
boundaryStatement =
  "The canonical trading object is a state-indexed proof-bearing admissible option cone. A blocked exposed state admits reduce and hold but not increase, which has no faithful ACT/HOLD/BAN label. Legacy BAN is therefore retained only as a coarse historical alarm/status, not as action or permission semantics."
