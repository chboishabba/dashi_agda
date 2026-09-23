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
  completeLocalJointRemainderBound : ConeDebtCoordinate
  coneAutomaticallyInsideCanonicalRadius : ConeDebtCoordinate
  coneContainedInFixedThreeUnitWindow : ConeDebtCoordinate
  fixedConeWindowZeroCountLogBound : ConeDebtCoordinate
  perConeLiteralSourceEnvelope : ConeDebtCoordinate
  coneMultiplicityBelowFixedWindowCount : ConeDebtCoordinate
  coneDebtLogOverR6Bound : ConeDebtCoordinate
  stripBoundSuppliesUniformQuarticFloor : ConeDebtCoordinate
  coneOnlyTargetCoefficientPayment : ConeDebtCoordinate

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
coneDebtStatus horizontalAlpha4RemainderBound = theoremOwned
coneDebtStatus completeLocalJointRemainderBound = theoremOwned
coneDebtStatus coneAutomaticallyInsideCanonicalRadius = theoremOwned
coneDebtStatus coneContainedInFixedThreeUnitWindow = theoremOwned
coneDebtStatus fixedConeWindowZeroCountLogBound = theoremOwned
coneDebtStatus perConeLiteralSourceEnvelope = theoremOwned
coneDebtStatus coneMultiplicityBelowFixedWindowCount = theoremOwned
coneDebtStatus coneDebtLogOverR6Bound = theoremOwned
coneDebtStatus stripBoundSuppliesUniformQuarticFloor = openAnalyticObstruction
coneDebtStatus coneOnlyTargetCoefficientPayment = openAnalyticObstruction

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
    completeLocalJointRemainderBoundPaid : Bool
    coneAutomaticallyInsideCanonicalRadiusPaid : Bool
    coneContainedInFixedThreeUnitWindowPaid : Bool
    fixedConeWindowZeroCountLogBoundPaid : Bool
    perConeLiteralSourceEnvelopePaid : Bool
    coneMultiplicityBelowFixedWindowCountPaid : Bool
    coneDebtLogOverR6BoundPaid : Bool
    stripBoundSuppliesUniformQuarticFloor : Bool
    coneOnlyTargetCoefficientPaymentPaid : Bool

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
    horizontalAlpha4RemainderBoundPaidIsTrue :
      horizontalAlpha4RemainderBoundPaid ≡ true
    completeLocalJointRemainderBoundPaidIsTrue :
      completeLocalJointRemainderBoundPaid ≡ true
    coneAutomaticallyInsideCanonicalRadiusPaidIsTrue :
      coneAutomaticallyInsideCanonicalRadiusPaid ≡ true
    coneContainedInFixedThreeUnitWindowPaidIsTrue :
      coneContainedInFixedThreeUnitWindowPaid ≡ true
    fixedConeWindowZeroCountLogBoundPaidIsTrue :
      fixedConeWindowZeroCountLogBoundPaid ≡ true
    perConeLiteralSourceEnvelopePaidIsTrue :
      perConeLiteralSourceEnvelopePaid ≡ true
    coneMultiplicityBelowFixedWindowCountPaidIsTrue :
      coneMultiplicityBelowFixedWindowCountPaid ≡ true
    coneDebtLogOverR6BoundPaidIsTrue :
      coneDebtLogOverR6BoundPaid ≡ true
    stripBoundSuppliesUniformQuarticFloorIsFalse :
      stripBoundSuppliesUniformQuarticFloor ≡ false
    coneOnlyTargetCoefficientPaymentPaidIsFalse :
      coneOnlyTargetCoefficientPaymentPaid ≡ false

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
    true true true false true true true true true
    true true true
    false false
    false false false
    refl refl refl refl refl
    refl refl refl refl refl refl refl refl refl
    refl refl refl
    refl refl
    refl refl refl
    "The literal off-ordinate G3 source is partitioned on finite symmetric zero windows into local cone, local good and far exact lanes.  The Taylor carrier is never globally summed.  ConeDebt is the positive part of the exact literal source on the potentially unfavorable cone, GoodQuarticGain is nonnegative, LocalRemainderDebt is finite-window absolute remainder debt, and FarExact retains the original decaying pair kernel.  The finite source obeys OffOrdExact <= ConeDebt - GoodQuarticGain + LocalRemainderDebt + FarExact.  The fail-fast compiler proves the absolute cone contribution has the correct O(log t / t^6) scale.  It also records that the strip condition 0<|a|<=1/2 by itself supplies no uniform positive quartic floor in a^4; this is a scaling diagnostic, not a claim that zeta zeros realize arbitrary horizontal offsets."
    "The canonical local radius eta0=1/(pi+1) is theorem-owned.  On this radius the horizontal quadratic jet error has the explicit bound |R_Q(q)| <= (5/96)|q|^4*M6.  Because M0=M2=0, the exact base cosine channel itself also satisfies |C_P(q)| <= (5/96)|q|^4*M4abs, so a sixth-order base remainder is not required merely to control the local debt.  The mixed cone is contained in the fixed window |gamma-t|<=3/2, and the enclosing three-unit zero multiplicity has an unconditional O(log t) bound from the existing local RvM theorem.  The hyperbolic alpha^4 remainder is source-written with the same certified 5/96 fourth-order constant, and the three local pieces compile to one explicit same-object bound for jointQuarticJetRemainder.  For t>=200 every mixed-cone zero is automatically inside the canonical local radius in both normalized coordinates.  The Lean companion further derives an explicit witness constant C_cone(W) with max(literal pair source,0) <= m_sigma*C_cone(W)/(t/16)^6 on every cone zero, proves the finite cone multiplicity is bounded by N(t-3/2,t+3/2), and compiles the local RvM theorem to ConeDebt_n <= 3*A0*C_cone(W)*log(t+5)/(t/16)^6.  A parametric target-payment compiler shows that any future target lower bound c*S(W)*a^4/(t/16)^6 would reduce absolute cone payment to the scalar comparison 3*A0*C_cone(W)*log(t+5) < c*S(W)*a^4.  Since the strip bound alone gives no positive floor for a^4, stop treating absolute cone payment as an independent route: investigate signed GoodGain/FarExact compensation or a modified witness."

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
