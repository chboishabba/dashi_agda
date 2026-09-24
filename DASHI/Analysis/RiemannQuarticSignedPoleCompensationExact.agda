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

compensationStatus exactOffOrdGlobalEqualsSubtypePairTsum = theoremOwned
compensationStatus eventualCompensationGapPaysCompletedResidual = theoremOwned
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

    exactOffOrdGlobalEqualsSubtypePairTsumPaidIsTrue :
      exactOffOrdGlobalEqualsSubtypePairTsumPaid ≡ true
    eventualCompensationGapPaysCompletedResidualPaidIsTrue :
      eventualCompensationGapPaysCompletedResidualPaid ≡ true
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
    true true false false
    refl refl refl refl refl
    refl refl refl
    refl refl refl refl
    "The fail-fast cone estimate has reached its natural absolute-value wall.  The preferred finite G3 budget preserves signed cancellation: LocalDebt = ConeDebt + LocalRemainderDebt, SignedCompensation = GoodQuarticGain - FarExact, and OffOrdExact <= LocalDebt - SignedCompensation.  The zero-extended global exact source is now theorem-welded to the existing subtype signedLiteralPairSourceTerm tsum, and an eventual positive compensation gap compiles through completedSignedResidual_eq_jointPairSource to the actual strict G3 consumer once its scalar target margin is paid.  FarExact is never replaced by an absolute allowance."
    "The same-object global tsum weld and the completed-residual compiler are now paid/source-written.  The only substantive producer question on this lane is whether the canonical cofinal exhaustion satisfies an eventual signed-compensation gap large enough to beat the exact scalar margin 4*D_comb(rho) + integral Psi_t*mu.  Do not split FarExact by absolute value unless a conventional proof forces that loss."

eventualCompensationGlobalCompilerIsPaid :
  compensationStatus eventualCompensationGapGlobalCompiler ≡ theoremOwned
eventualCompensationGlobalCompilerIsPaid = refl

globalSubtypeTsumWeldIsPaid :
  compensationStatus exactOffOrdGlobalEqualsSubtypePairTsum ≡ theoremOwned
globalSubtypeTsumWeldIsPaid = refl

compensationGapRemainsAnalytic :
  compensationStatus eventualCompensationGapExists ≡ openAnalyticObstruction
compensationGapRemainsAnalytic = refl


------------------------------------------------------------------------
-- HUMAN-FACING COMPENSATION MIN-CUT
--
-- The auxiliary scalar margin used by the Lean compiler is deliberately
-- hidden from the conventional statement.
--
-- Define
--
--   T_W(rho)
--     = 4 * D_comb(rho) + integral Psi_t * mu.
--
-- The authoritative analytic hypothesis is:
--
--   exists eps > 0, exists N,
--   forall n >= N,
--
--     LocalDebt_n - SignedCompensation_n
--       <= T_W(rho) - eps.
--
-- The Lean companion proves this single hypothesis implies the strict G3
-- completed-residual inequality by choosing the old auxiliary margin
-- internally as T_W(rho) - eps/2.
------------------------------------------------------------------------

data HumanFacingCompensationCoordinate : Set where
  compensationTargetThresholdDefinition :
    HumanFacingCompensationCoordinate
  uniformPositiveCompensationGapStatement :
    HumanFacingCompensationCoordinate
  uniformPositiveCompensationGapCompilerToG3 :
    HumanFacingCompensationCoordinate
  uniformPositiveCompensationGapProved :
    HumanFacingCompensationCoordinate

humanFacingCompensationStatus :
  HumanFacingCompensationCoordinate -> CompensationStatus
humanFacingCompensationStatus compensationTargetThresholdDefinition =
  theoremOwned
humanFacingCompensationStatus uniformPositiveCompensationGapStatement =
  theoremOwned
humanFacingCompensationStatus uniformPositiveCompensationGapCompilerToG3 =
  theoremOwned
humanFacingCompensationStatus uniformPositiveCompensationGapProved =
  openAnalyticObstruction

record HumanFacingCompensationBoundary : Set where
  constructor human-facing-compensation-boundary
  field
    targetThresholdDefinitionPaid : Bool
    uniformGapStatementPaid : Bool
    uniformGapCompilerToG3Paid : Bool
    uniformGapProved : Bool

    targetThresholdDefinitionPaidIsTrue :
      targetThresholdDefinitionPaid ≡ true
    uniformGapStatementPaidIsTrue :
      uniformGapStatementPaid ≡ true
    uniformGapCompilerToG3PaidIsTrue :
      uniformGapCompilerToG3Paid ≡ true
    uniformGapProvedIsFalse :
      uniformGapProved ≡ false

    paperStatement : String
    researchInstruction : String

canonicalHumanFacingCompensationBoundary :
  HumanFacingCompensationBoundary
canonicalHumanFacingCompensationBoundary =
  human-facing-compensation-boundary
    true true true false
    refl refl refl refl
    "The Clay-facing analytic min-cut is one uniform epsilon gap at the canonical local radius: there exist eps>0 and N such that for every n>=N, LocalDebt_n - SignedCompensation_n <= T_W(rho)-eps, where T_W(rho)=4*D_comb(rho)+integral Psi_t*mu.  The auxiliary compiler scalar M is not part of the human theorem."
    "Stop formal recutting here.  Prove or falsify the uniform signed-compensation gap using the actual zero distribution while preserving the signed GoodGain/FarExact correlation.  If the gap fails under plausible admissible configurations, redesign the witness rather than adding more compiler layers."

uniformGapCompilerIsPaid :
  humanFacingCompensationStatus
    uniformPositiveCompensationGapCompilerToG3
    ≡ theoremOwned
uniformGapCompilerIsPaid = refl

uniformGapIsTheAnalyticWall :
  humanFacingCompensationStatus
    uniformPositiveCompensationGapProved
    ≡ openAnalyticObstruction
uniformGapIsTheAnalyticWall = refl


------------------------------------------------------------------------
-- SHARPENED COMPENSATION AFTER SAME-ORDINATE SIGN DISCOVERY
--
-- The Lean companion proves the exact same-ordinate normalized pair identity
--
--   K_W(alpha,0) = -4 * D_W(alpha).
--
-- Hence every nonzero alpha in the paid target band has K_W(alpha,0)<0.
-- A same-object q-Lipschitz theorem then gives a nonempty interval
--
--   |q| < q0 <= |alpha|
--
-- on which the exact pair kernel remains strictly negative.  This interval
-- lies inside the nominal mixed cone q^2 < 6 alpha^2.
--
-- Therefore the conservative ConeDebt abstraction discards genuine favorable
-- mass.  The sharpened finite budget splits the exact cone source itself:
--
--   ConeExact = ConeDebt - ConeGain,
--
-- and uses
--
--   SharpenedLocalDebt
--     = ConeDebt + GoodRemainderDebt
--
--   SharpenedSignedCompensation
--     = ConeGain + GoodGain - FarExact.
--
-- The resulting sharpened budget is theorem-proved no larger than the old
-- conservative joint budget, and every old uniform compensation proof implies
-- the sharpened one.
------------------------------------------------------------------------

data SharpenedCompensationCoordinate : Set where
  sameOrdinatePairKernelEqualsNegFourTarget :
    SharpenedCompensationCoordinate
  favorableNegativeConeCoreExists :
    SharpenedCompensationCoordinate
  coneGainDefinition :
    SharpenedCompensationCoordinate
  coneExactEqualsDebtMinusGain :
    SharpenedCompensationCoordinate
  goodOnlyRemainderDebt :
    SharpenedCompensationCoordinate
  sharpenedFiniteBudget :
    SharpenedCompensationCoordinate
  sharpenedGlobalCompilerToG3 :
    SharpenedCompensationCoordinate
  sharpenedBudgetBelowConservativeBudget :
    SharpenedCompensationCoordinate
  conservativeGapImpliesSharpenedGap :
    SharpenedCompensationCoordinate
  sharpenedUniformGapProved :
    SharpenedCompensationCoordinate

sharpenedCompensationStatus :
  SharpenedCompensationCoordinate -> CompensationStatus
sharpenedCompensationStatus sameOrdinatePairKernelEqualsNegFourTarget =
  theoremOwned
sharpenedCompensationStatus favorableNegativeConeCoreExists =
  theoremOwned
sharpenedCompensationStatus coneGainDefinition =
  theoremOwned
sharpenedCompensationStatus coneExactEqualsDebtMinusGain =
  theoremOwned
sharpenedCompensationStatus goodOnlyRemainderDebt =
  theoremOwned
sharpenedCompensationStatus sharpenedFiniteBudget =
  theoremOwned
sharpenedCompensationStatus sharpenedGlobalCompilerToG3 =
  theoremOwned
sharpenedCompensationStatus sharpenedBudgetBelowConservativeBudget =
  theoremOwned
sharpenedCompensationStatus conservativeGapImpliesSharpenedGap =
  theoremOwned
sharpenedCompensationStatus sharpenedUniformGapProved =
  openAnalyticObstruction

sameOrdinateKernelSignIsPaid :
  sharpenedCompensationStatus sameOrdinatePairKernelEqualsNegFourTarget
    ≡ theoremOwned
sameOrdinateKernelSignIsPaid = refl

favorableConeCoreIsPaid :
  sharpenedCompensationStatus favorableNegativeConeCoreExists
    ≡ theoremOwned
favorableConeCoreIsPaid = refl

sharpenedGapIsCurrentAnalyticWall :
  sharpenedCompensationStatus sharpenedUniformGapProved
    ≡ openAnalyticObstruction
sharpenedGapIsCurrentAnalyticWall = refl
