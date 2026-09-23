module DASHI.Analysis.RiemannQuarticSignedPoleCompensationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- RH G3 SIGNED COMPENSATION OWNER
--
-- Lean companion:
--
--   Synthesis/RiemannProjectiveQuarticFourWindowSignedPoleConeDecomposition.lean
--
-- After the fail-fast absolute cone payment, the authoritative finite
-- conventional budget is no longer three independent absolute obligations.
--
-- Define on the canonical symmetric finite zero exhaustion:
--
--   LocalDebt_n
--     = ConeDebt_n + LocalRemainderDebt_n
--
--   SignedCompensation_n
--     = GoodQuarticGain_n - FarExact_n
--
-- Then the exact off-ordinate literal source satisfies
--
--   OffOrdExact_n
--     <= LocalDebt_n - SignedCompensation_n.
--
-- Hence an eventual inequality
--
--   LocalDebt_n < SignedCompensation_n + margin
--
-- compiles to a global upper bound for the exact off-ordinate source.
--
-- The point of this owner is methodological as well as formal: FarExact keeps
-- its sign.  It is not replaced by an absolute allowance merely to make the
-- bookkeeping modular.
------------------------------------------------------------------------

data CompensationCoordinate : Set where
  localDebtDefinition : CompensationCoordinate
  signedCompensationDefinition : CompensationCoordinate
  finiteJointBudgetDefinition : CompensationCoordinate
  finiteExactSourceBelowJointBudget : CompensationCoordinate
  finiteCompensationGapCompiler : CompensationCoordinate

  exactOffOrdZeroExtensionSummable : CompensationCoordinate
  exactOffOrdCofinalLimit : CompensationCoordinate
  eventualCompensationGapGlobalCompiler : CompensationCoordinate

  exactOffOrdGlobalEqualsSubtypePairTsum : CompensationCoordinate
  eventualCompensationGapPaysCompletedResidual : CompensationCoordinate
  eventualCompensationGapExists : CompensationCoordinate
  g3StrictTargetBound : CompensationCoordinate

data CompensationStatus : Set where
  theoremOwned : CompensationStatus
  openAssembly : CompensationStatus
  openAnalyticObstruction : CompensationStatus

compensationStatus : CompensationCoordinate -> CompensationStatus
compensationStatus localDebtDefinition = theoremOwned
compensationStatus signedCompensationDefinition = theoremOwned
compensationStatus finiteJointBudgetDefinition = theoremOwned
compensationStatus finiteExactSourceBelowJointBudget = theoremOwned
compensationStatus finiteCompensationGapCompiler = theoremOwned

compensationStatus exactOffOrdZeroExtensionSummable = theoremOwned
compensationStatus exactOffOrdCofinalLimit = theoremOwned
compensationStatus eventualCompensationGapGlobalCompiler = theoremOwned

compensationStatus exactOffOrdGlobalEqualsSubtypePairTsum = openAssembly
compensationStatus eventualCompensationGapPaysCompletedResidual = openAssembly
compensationStatus eventualCompensationGapExists = openAnalyticObstruction
compensationStatus g3StrictTargetBound = openAnalyticObstruction

record QuarticSignedPoleCompensationBoundary : Set where
  constructor quartic-signed-pole-compensation-boundary
  field
    localDebtDefinitionPaid : Bool
    signedCompensationDefinitionPaid : Bool
    finiteJointBudgetDefinitionPaid : Bool
    finiteExactSourceBelowJointBudgetPaid : Bool
    finiteCompensationGapCompilerPaid : Bool

    exactOffOrdZeroExtensionSummablePaid : Bool
    exactOffOrdCofinalLimitPaid : Bool
    eventualCompensationGapGlobalCompilerPaid : Bool

    exactOffOrdGlobalEqualsSubtypePairTsumPaid : Bool
    eventualCompensationGapPaysCompletedResidualPaid : Bool
    eventualCompensationGapExistsPaid : Bool
    g3StrictTargetBoundPaid : Bool

    localDebtDefinitionPaidIsTrue :
      localDebtDefinitionPaid ≡ true
    signedCompensationDefinitionPaidIsTrue :
      signedCompensationDefinitionPaid ≡ true
    finiteJointBudgetDefinitionPaidIsTrue :
      finiteJointBudgetDefinitionPaid ≡ true
    finiteExactSourceBelowJointBudgetPaidIsTrue :
      finiteExactSourceBelowJointBudgetPaid ≡ true
    finiteCompensationGapCompilerPaidIsTrue :
      finiteCompensationGapCompilerPaid ≡ true

    exactOffOrdZeroExtensionSummablePaidIsTrue :
      exactOffOrdZeroExtensionSummablePaid ≡ true
    exactOffOrdCofinalLimitPaidIsTrue :
      exactOffOrdCofinalLimitPaid ≡ true
    eventualCompensationGapGlobalCompilerPaidIsTrue :
      eventualCompensationGapGlobalCompilerPaid ≡ true

    exactOffOrdGlobalEqualsSubtypePairTsumPaidIsFalse :
      exactOffOrdGlobalEqualsSubtypePairTsumPaid ≡ false
    eventualCompensationGapPaysCompletedResidualPaidIsFalse :
      eventualCompensationGapPaysCompletedResidualPaid ≡ false
    eventualCompensationGapExistsPaidIsFalse :
      eventualCompensationGapExistsPaid ≡ false
    g3StrictTargetBoundPaidIsFalse :
      g3StrictTargetBoundPaid ≡ false

    interpretation : String
    nextResearchCut : String

canonicalQuarticSignedPoleCompensationBoundary :
  QuarticSignedPoleCompensationBoundary
canonicalQuarticSignedPoleCompensationBoundary =
  quartic-signed-pole-compensation-boundary
    true true true true true
    true true true
    false false false false
    refl refl refl refl refl
    refl refl refl
    refl refl refl refl
    "The fail-fast cone estimate has reached its natural absolute-value wall.  The preferred finite G3 budget now preserves signed cancellation: LocalDebt = ConeDebt + LocalRemainderDebt, SignedCompensation = GoodQuarticGain - FarExact, and OffOrdExact <= LocalDebt - SignedCompensation.  A theorem-bearing cofinal compiler shows that an eventual positive compensation gap gives a global upper bound on the exact off-ordinate zero-extended source.  This is strictly stronger research discipline than turning FarExact into another absolute debt coordinate."
    "First close the small same-object assembly weld between the zero-extended global off-ordinate tsum and the existing subtype signedLiteralPairSourceTerm tsum used by completedSignedResidual_eq_jointPairSource.  Then the only substantive producer question is whether the canonical cofinal exhaustion satisfies an eventual signed-compensation gap large enough to pay the target margin.  Do not split FarExact by absolute value unless a conventional proof forces that loss."

eventualCompensationGlobalCompilerIsPaid :
  compensationStatus eventualCompensationGapGlobalCompiler ≡ theoremOwned
eventualCompensationGlobalCompilerIsPaid = refl

globalSubtypeTsumWeldRemainsOpen :
  compensationStatus exactOffOrdGlobalEqualsSubtypePairTsum ≡ openAssembly
globalSubtypeTsumWeldRemainsOpen = refl

compensationGapRemainsAnalytic :
  compensationStatus eventualCompensationGapExists ≡ openAnalyticObstruction
compensationGapRemainsAnalytic = refl
