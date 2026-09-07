module DASHI.Physics.Closure.NSTriadKNR423FixedOutputProducerProofSearchRound488Exact where

------------------------------------------------------------------------
-- ROUND488 / FIRST-MISSING SEARCH INSIDE THE CONCRETE R487 PRODUCER ROUTE
--
-- The terminal consumer remains R423 itself.  R487 is only a sufficient
-- producer route, but it is now exact enough to expose its own dependency DAG:
--
--   fixed-output theorem family:  C_k <= B_k
--                 |
--                 v
--   cutoff-uniform budget sum:     4 sum_k B_k <= B(T)
--                 |
--                 v
--   exact R423 QuadraticCompanionSignedPayment.
--
-- R232 rules out the generic pointwise half-derivative route in the comparable
-- region and redirects to SAME-SCALE SUMMED cancellation.  R294 proves that a
-- swap-invariant weight preserves the complete fixed-output product-rule ->
-- mixed-commutator collapse before norms.  It does not pay that commutator.
--
-- Hence the first mathematical producer search is local and signed: establish
-- the fixed-output payment family on the literal weighted commutator/companion
-- carrier.  Only after those theorem-bearing budgets exist should search move
-- to their cutoff-uniform global sum.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Core.ProofSearchLeastPrivilegeAdmissionExact as Least
import DASHI.Physics.Closure.NSTriadKNOppositeHelicityDyadicDecisionRound232Exact as R232
import DASHI.Physics.Closure.NSTriadKNResolventWeightedMixedCommutatorRound294Exact as R294
import DASHI.Physics.Closure.NSTriadKNQuadraticCompanionSignedHeatToBarrierRound423Exact as R423
import DASHI.Physics.Closure.NSTriadKNFixedOutputSignedCrossAggregationRound432Exact as R432
import DASHI.Physics.Closure.NSTriadKNFixedOutputPaymentsToR423Round487Exact as R487

------------------------------------------------------------------------
-- Producer-route state.
------------------------------------------------------------------------

data R423ProducerResidual : Set where
  missingFixedOutputPaymentFamily : R423ProducerResidual
  missingCutoffUniformBudgetSum : R423ProducerResidual
  producerRouteClosed : R423ProducerResidual

record R423ProducerStatus : Set where
  constructor r423-producer-status
  field
    fixedOutputPaymentFamilyPresent : Bool
    cutoffUniformBudgetSumPresent : Bool

open R423ProducerStatus public

firstR423ProducerResidual : R423ProducerStatus → R423ProducerResidual
firstR423ProducerResidual (r423-producer-status false sumPresent) =
  missingFixedOutputPaymentFamily
firstR423ProducerResidual (r423-producer-status true false) =
  missingCutoffUniformBudgetSum
firstR423ProducerResidual (r423-producer-status true true) =
  producerRouteClosed

------------------------------------------------------------------------
-- Search mechanism.
------------------------------------------------------------------------

data SearchMechanism : Set where
  ThinkSameScaleSummedCancellation : SearchMechanism
  ThinkCutoffUniformBudgetAggregation : SearchMechanism
  CompileR423 : SearchMechanism

mechanismFor : R423ProducerResidual → SearchMechanism
mechanismFor missingFixedOutputPaymentFamily = ThinkSameScaleSummedCancellation
mechanismFor missingCutoffUniformBudgetSum = ThinkCutoffUniformBudgetAggregation
mechanismFor producerRouteClosed = CompileR423

currentProducerStatus : R423ProducerStatus
currentProducerStatus = r423-producer-status false false

currentFirstMissing :
  firstR423ProducerResidual currentProducerStatus
  ≡ missingFixedOutputPaymentFamily
currentFirstMissing = refl

currentMechanism :
  mechanismFor (firstR423ProducerResidual currentProducerStatus)
  ≡ ThinkSameScaleSummedCancellation
currentMechanism = refl

afterLocalPaymentsStatus : R423ProducerStatus
afterLocalPaymentsStatus = r423-producer-status true false

afterLocalPaymentsFirstMissing :
  firstR423ProducerResidual afterLocalPaymentsStatus
  ≡ missingCutoffUniformBudgetSum
afterLocalPaymentsFirstMissing = refl

afterLocalPaymentsMechanism :
  mechanismFor (firstR423ProducerResidual afterLocalPaymentsStatus)
  ≡ ThinkCutoffUniformBudgetAggregation
afterLocalPaymentsMechanism = refl

------------------------------------------------------------------------
-- Least-privilege route dispositions.
------------------------------------------------------------------------

directR423Disposition : Least.RouteDisposition
directR423Disposition = Least.admitted

r487FixedOutputProducerDisposition : Least.RouteDisposition
r487FixedOutputProducerDisposition = Least.admitted

pointwiseHalfDerivativeDisposition : Least.RouteDisposition
pointwiseHalfDerivativeDisposition = Least.rejected Least.noGoCollision

absoluteCellwiseMajorizationDisposition : Least.RouteDisposition
absoluteCellwiseMajorizationDisposition = Least.rejected Least.strengthMismatch

crossOutputCoherenceDisposition : Least.RouteDisposition
crossOutputCoherenceDisposition = Least.rejected Least.alreadyOwned

r284MandatoryDisposition : Least.RouteDisposition
r284MandatoryDisposition = Least.rejected Least.hypothesisInflation

------------------------------------------------------------------------
-- Exact pins to repo-owned search facts.
------------------------------------------------------------------------

pointwiseComparableGainRuledOut :
  R232.round232CCGenericPointwiseHalfDerivativeGainExists ≡ false
pointwiseComparableGainRuledOut =
  R232.round232CCGenericPointwiseHalfDerivativeGainExistsIsFalse

sameScaleSummedCancellationSelected :
  R232.round232NextTargetIsSameScaleSummedCancellation ≡ true
sameScaleSummedCancellationSelected =
  R232.round232NextTargetIsSameScaleSummedCancellationIsTrue

weightedCommutatorCollapseAlreadyOwned :
  R294.round294GenericSwapInvariantWeightedCollapseClosed ≡ true
weightedCommutatorCollapseAlreadyOwned =
  R294.round294GenericSwapInvariantWeightedCollapseClosedIsTrue

weightedCommutatorPaymentStillOpen :
  R294.round294WeightedNonlinearCommutatorPaid ≡ false
weightedCommutatorPaymentStillOpen = refl

crossOutputCoherenceNotRequired :
  R432.round432CrossOutputCoherencePaymentRequired ≡ false
crossOutputCoherenceNotRequired =
  R432.round432CrossOutputCoherencePaymentRequiredIsFalse

r487CompilerClosed : R487.round487R432ToR423CompilerClosed ≡ true
r487CompilerClosed = refl

r487LocalPaymentsStillOpen :
  R487.round487PhysicalFixedOutputPaymentsClosed ≡ false
r487LocalPaymentsStillOpen = refl

r487UniformBudgetSumStillOpen :
  R487.round487CutoffUniformFibreBudgetSumClosed ≡ false
r487UniformBudgetSumStillOpen = refl

------------------------------------------------------------------------
-- No-collapse boundaries.
------------------------------------------------------------------------

data WeightedCollapsePaysCommutator : Set where
data LocalPaymentsAutomaticallyPayUniformSum : Set where
data OptionalProducerBecomesMandatory : Set where

weightedCollapseDoesNotPayCommutator : WeightedCollapsePaysCommutator → ⊥
weightedCollapseDoesNotPayCommutator ()

localPaymentsDoNotAutomaticallyPayUniformSum :
  LocalPaymentsAutomaticallyPayUniformSum → ⊥
localPaymentsDoNotAutomaticallyPayUniformSum ()

optionalProducerDoesNotBecomeMandatory : OptionalProducerBecomesMandatory → ⊥
optionalProducerDoesNotBecomeMandatory ()

------------------------------------------------------------------------
-- Ledger.
------------------------------------------------------------------------

round488CanonicalTerminalConsumerRemainsR423 : Bool
round488CanonicalTerminalConsumerRemainsR423 = true

round488R487IsSufficientProducerNotNewTerminalTarget : Bool
round488R487IsSufficientProducerNotNewTerminalTarget = true

round488CurrentFirstMissingIsFixedOutputPaymentFamily : Bool
round488CurrentFirstMissingIsFixedOutputPaymentFamily = true

round488CurrentMechanismIsSameScaleSummedCancellation : Bool
round488CurrentMechanismIsSameScaleSummedCancellation = true

round488PointwiseHalfDerivativeRouteRejected : Bool
round488PointwiseHalfDerivativeRouteRejected = true

round488WeightedCommutatorAlreadyPaid : Bool
round488WeightedCommutatorAlreadyPaid = false

round488CutoffUniformBudgetSumClosed : Bool
round488CutoffUniformBudgetSumClosed = false

round488R423SignedCompanionBudgetClosed : Bool
round488R423SignedCompanionBudgetClosed = false

round488PackageAClosed : Bool
round488PackageAClosed = false

round488ClayPromotion : Bool
round488ClayPromotion = false

round488WeightedCommutatorAlreadyPaidIsFalse :
  round488WeightedCommutatorAlreadyPaid ≡ false
round488WeightedCommutatorAlreadyPaidIsFalse = refl

round488R423SignedCompanionBudgetClosedIsFalse :
  round488R423SignedCompanionBudgetClosed ≡ false
round488R423SignedCompanionBudgetClosedIsFalse = refl

round488ClayPromotionIsFalse : round488ClayPromotion ≡ false
round488ClayPromotionIsFalse = refl
