module DASHI.Analysis.RiemannQuarticSignedPoleConeDebtExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- RH G3 CONE / GOOD / FAR DEBT OWNER
--
-- Lean companions:
--
--   Synthesis/RiemannProjectiveQuarticFourWindowSignedPoleConeDecomposition.lean
--   Synthesis/RiemannProjectiveQuarticFourWindowSignedPoleLocalRemainderBounds.lean
--
-- The joint quartic Taylor carrier is used only on a fixed normalized local
-- region.  The far carrier remains the exact decaying literal pair kernel.
--
-- The local region is split into:
--
--   cone : delta^2 <= 6 a^2
--   good : 6 a^2 < delta^2.
--
-- On finite symmetric zero windows the exact source satisfies the
-- theorem-bearing scalar budget
--
--   OffOrdExact
--     <= ConeDebt
--        - GoodQuarticGain
--        + LocalRemainderDebt
--        + FarExact.
--
-- ConeDebt is the positive part of the exact literal source on the cone.
-- GoodQuarticGain is nonnegative by the paid mixed-sign quartic theorem.
-- FarExact is never Taylor-expanded.
------------------------------------------------------------------------

data ConeDebtCoordinate : Set where
  coneGoodFarPartition : ConeDebtCoordinate
  exactFiniteSourcePartition : ConeDebtCoordinate
  coneDebtNonnegative : ConeDebtCoordinate
  goodQuarticGainNonnegative : ConeDebtCoordinate
  finiteConeDebtBudget : ConeDebtCoordinate

  canonicalLocalRadius : ConeDebtCoordinate
  horizontalQuadraticQ4RemainderBound : ConeDebtCoordinate
  exactBaseQuarticLocalBound : ConeDebtCoordinate
  baseQ6RemainderBound : ConeDebtCoordinate
  horizontalAlpha4RemainderBound : ConeDebtCoordinate
  coneContainedInFixedThreeUnitWindow : ConeDebtCoordinate
  fixedConeWindowZeroCountLogBound : ConeDebtCoordinate

  coneDebtGloballyPayable : ConeDebtCoordinate
  farExactContributionControlled : ConeDebtCoordinate
  finiteBudgetClosesG3 : ConeDebtCoordinate

data ConeDebtStatus : Set where
  theoremOwned : ConeDebtStatus
  openAnalyticObstruction : ConeDebtStatus

coneDebtStatus : ConeDebtCoordinate -> ConeDebtStatus
coneDebtStatus coneGoodFarPartition = theoremOwned
coneDebtStatus exactFiniteSourcePartition = theoremOwned
coneDebtStatus coneDebtNonnegative = theoremOwned
coneDebtStatus goodQuarticGainNonnegative = theoremOwned
coneDebtStatus finiteConeDebtBudget = theoremOwned

coneDebtStatus canonicalLocalRadius = theoremOwned
coneDebtStatus horizontalQuadraticQ4RemainderBound = theoremOwned
coneDebtStatus exactBaseQuarticLocalBound = theoremOwned
coneDebtStatus baseQ6RemainderBound = openAnalyticObstruction
coneDebtStatus horizontalAlpha4RemainderBound = openAnalyticObstruction
coneDebtStatus coneContainedInFixedThreeUnitWindow = theoremOwned
coneDebtStatus fixedConeWindowZeroCountLogBound = theoremOwned

coneDebtStatus coneDebtGloballyPayable = openAnalyticObstruction
coneDebtStatus farExactContributionControlled = openAnalyticObstruction
coneDebtStatus finiteBudgetClosesG3 = openAnalyticObstruction

record QuarticSignedPoleConeDebtBoundary : Set where
  constructor quartic-signed-pole-cone-debt-boundary
  field
    coneGoodFarPartitionPaid : Bool
    exactFiniteSourcePartitionPaid : Bool
    coneDebtNonnegativePaid : Bool
    goodQuarticGainNonnegativePaid : Bool
    finiteConeDebtBudgetPaid : Bool

    canonicalLocalRadiusPaid : Bool
    horizontalQuadraticQ4RemainderBoundPaid : Bool
    exactBaseQuarticLocalBoundPaid : Bool
    baseQ6RemainderBoundPaid : Bool
    horizontalAlpha4RemainderBoundPaid : Bool
    coneContainedInFixedThreeUnitWindowPaid : Bool
    fixedConeWindowZeroCountLogBoundPaid : Bool

    coneDebtGloballyPayablePaid : Bool
    farExactContributionControlledPaid : Bool
    finiteBudgetClosesG3Paid : Bool

    coneGoodFarPartitionPaidIsTrue :
      coneGoodFarPartitionPaid ≡ true
    exactFiniteSourcePartitionPaidIsTrue :
      exactFiniteSourcePartitionPaid ≡ true
    coneDebtNonnegativePaidIsTrue :
      coneDebtNonnegativePaid ≡ true
    goodQuarticGainNonnegativePaidIsTrue :
      goodQuarticGainNonnegativePaid ≡ true
    finiteConeDebtBudgetPaidIsTrue :
      finiteConeDebtBudgetPaid ≡ true

    canonicalLocalRadiusPaidIsTrue :
      canonicalLocalRadiusPaid ≡ true
    horizontalQuadraticQ4RemainderBoundPaidIsTrue :
      horizontalQuadraticQ4RemainderBoundPaid ≡ true
    exactBaseQuarticLocalBoundPaidIsTrue :
      exactBaseQuarticLocalBoundPaid ≡ true
    baseQ6RemainderBoundPaidIsFalse :
      baseQ6RemainderBoundPaid ≡ false
    horizontalAlpha4RemainderBoundPaidIsFalse :
      horizontalAlpha4RemainderBoundPaid ≡ false
    coneContainedInFixedThreeUnitWindowPaidIsTrue :
      coneContainedInFixedThreeUnitWindowPaid ≡ true
    fixedConeWindowZeroCountLogBoundPaidIsTrue :
      fixedConeWindowZeroCountLogBoundPaid ≡ true

    coneDebtGloballyPayablePaidIsFalse :
      coneDebtGloballyPayablePaid ≡ false
    farExactContributionControlledPaidIsFalse :
      farExactContributionControlledPaid ≡ false
    finiteBudgetClosesG3PaidIsFalse :
      finiteBudgetClosesG3Paid ≡ false

    interpretation : String
    nextResearchCut : String

canonicalQuarticSignedPoleConeDebtBoundary :
  QuarticSignedPoleConeDebtBoundary
canonicalQuarticSignedPoleConeDebtBoundary =
  quartic-signed-pole-cone-debt-boundary
    true true true true true
    true true true false false true true
    false false false
    refl refl refl refl refl
    refl refl refl refl refl refl refl
    refl refl refl
    "The literal off-ordinate G3 source is now partitioned on finite symmetric zero windows into local cone, local good and far exact lanes.  The Taylor carrier is never globally summed.  ConeDebt is the positive part of the exact literal source on the potentially unfavorable cone, GoodQuarticGain is nonnegative, LocalRemainderDebt is finite-window absolute remainder debt, and FarExact retains the original decaying pair kernel.  The finite source obeys OffOrdExact <= ConeDebt - GoodQuarticGain + LocalRemainderDebt + FarExact."
    "The canonical local radius eta0=1/(pi+1) is theorem-owned.  On this radius the horizontal quadratic jet error has the explicit bound |R_Q(q)| <= (5/96)|q|^4*M6.  Because M0=M2=0, the exact base cosine channel itself also satisfies |C_P(q)| <= (5/96)|q|^4*M4abs, so a sixth-order base remainder is not required merely to control the local debt.  The mixed cone is contained in the fixed window |gamma-t|<=3/2, and the enclosing three-unit zero multiplicity has an unconditional O(log t) bound from the existing local RvM theorem.  The remaining local analytic estimate needed for a direct debt bound is the hyperbolic alpha^4 remainder.  After that, test whether the weighted cone debt can actually be paid from the fixed-window zero information before adding more formal structure."

finiteConeDebtBudgetIsPaid :
  coneDebtStatus finiteConeDebtBudget ≡ theoremOwned
finiteConeDebtBudgetIsPaid = refl

horizontalQ4RemainderIsPaid :
  coneDebtStatus horizontalQuadraticQ4RemainderBound ≡ theoremOwned
horizontalQ4RemainderIsPaid = refl

baseQ6RemainderRemainsOpen :
  coneDebtStatus baseQ6RemainderBound ≡ openAnalyticObstruction
baseQ6RemainderRemainsOpen = refl

coneDebtPaymentRemainsOpen :
  coneDebtStatus coneDebtGloballyPayable ≡ openAnalyticObstruction
coneDebtPaymentRemainsOpen = refl
