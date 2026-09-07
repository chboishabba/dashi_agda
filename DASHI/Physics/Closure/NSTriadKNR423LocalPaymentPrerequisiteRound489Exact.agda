module DASHI.Physics.Closure.NSTriadKNR423LocalPaymentPrerequisiteRound489Exact where

------------------------------------------------------------------------
-- ROUND489 / LOCAL R423 PAYMENT: DIRECT SIGNED PAYMENT IS CANONICAL
--
-- R423 itself does not require a Laplace representation.  Its primitive
-- consumer asks for the integrated signed companion scalar, the same-object
-- R406 = 4 * cross identity, and a cutoff-uniform upper budget.  R487 makes
-- this explicit by setting the signed-heat and quadratic-companion scalars to
-- the same fixed-output aggregate definitionally.
--
-- Therefore the canonical direct route is:
--
--   same-output/same-scale signed spacetime payment  ->  R487  ->  R423.
--
-- The R490/R491 Laplace realization remains an admitted sufficient producer
-- strategy for constructing that payment, but its standard-analysis authority
-- is NOT a prerequisite of the direct R423 consumer.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Core.ProofSearchLeastPrivilegeAdmissionExact as Least
import DASHI.Physics.Closure.NSTriadKNCellRateSwapInvariantWeightRound295Exact as R295
import DASHI.Physics.Closure.NSTriadKNHeatFactorizedPairRemainderRound299Exact as R299
import DASHI.Physics.Closure.NSTriadKNPhysicalHeatDoubleSumFactorizationRound440Exact as R440
import DASHI.Physics.Closure.NSTriadKNQuadraticCompanionSignedHeatToBarrierRound423Exact as R423
import DASHI.Physics.Closure.NSTriadKNFixedOutputPaymentsToR423Round487Exact as R487
import DASHI.Physics.Closure.NSTriadKNR423FixedOutputProducerProofSearchRound488Exact as R488

------------------------------------------------------------------------
-- Canonical direct-route scheduler.
------------------------------------------------------------------------

data DirectPaymentResidual : Set where
  missingSignedSpacetimeEstimate : DirectPaymentResidual
  missingCutoffUniformBudgetSum : DirectPaymentResidual
  directPaymentClosed : DirectPaymentResidual

record DirectPaymentStatus : Set where
  constructor direct-payment-status
  field
    signedSpacetimeEstimatePresent : Bool
    cutoffUniformBudgetSumPresent : Bool

open DirectPaymentStatus public

firstDirectResidual : DirectPaymentStatus → DirectPaymentResidual
firstDirectResidual (direct-payment-status false budget) =
  missingSignedSpacetimeEstimate
firstDirectResidual (direct-payment-status true false) =
  missingCutoffUniformBudgetSum
firstDirectResidual (direct-payment-status true true) =
  directPaymentClosed

data DirectMechanism : Set where
  ThinkSameScaleSignedSpacetime : DirectMechanism
  ThinkCutoffUniformBudgetAggregation : DirectMechanism
  CompileR487ToR423 : DirectMechanism

mechanismFor : DirectPaymentResidual → DirectMechanism
mechanismFor missingSignedSpacetimeEstimate = ThinkSameScaleSignedSpacetime
mechanismFor missingCutoffUniformBudgetSum = ThinkCutoffUniformBudgetAggregation
mechanismFor directPaymentClosed = CompileR487ToR423

currentDirectStatus : DirectPaymentStatus
currentDirectStatus = direct-payment-status false false

currentFirstDirectResidual :
  firstDirectResidual currentDirectStatus ≡ missingSignedSpacetimeEstimate
currentFirstDirectResidual = refl

currentDirectMechanism :
  mechanismFor (firstDirectResidual currentDirectStatus)
  ≡ ThinkSameScaleSignedSpacetime
currentDirectMechanism = refl

afterLocalPaymentStatus : DirectPaymentStatus
afterLocalPaymentStatus = direct-payment-status true false

afterLocalPaymentFirstResidual :
  firstDirectResidual afterLocalPaymentStatus ≡ missingCutoffUniformBudgetSum
afterLocalPaymentFirstResidual = refl

------------------------------------------------------------------------
-- Optional Laplace producer lane.
------------------------------------------------------------------------

data LaplaceProducerResidual : Set where
  missingStandardLaplaceAuthority : LaplaceProducerResidual
  missingLaplaceLaneSignedEstimate : LaplaceProducerResidual
  laplaceProducerClosed : LaplaceProducerResidual

record LaplaceProducerStatus : Set where
  constructor laplace-producer-status
  field
    standardLaplaceAuthorityPresent : Bool
    laplaceLaneSignedEstimatePresent : Bool

firstLaplaceProducerResidual :
  LaplaceProducerStatus → LaplaceProducerResidual
firstLaplaceProducerResidual (laplace-producer-status false estimate) =
  missingStandardLaplaceAuthority
firstLaplaceProducerResidual (laplace-producer-status true false) =
  missingLaplaceLaneSignedEstimate
firstLaplaceProducerResidual (laplace-producer-status true true) =
  laplaceProducerClosed

------------------------------------------------------------------------
-- Exact pins to owned infrastructure.
------------------------------------------------------------------------

cellRateFunctionAlreadyBuildsSwapInvariantWeight :
  R295.round295AnyFunctionOfCellRatePreservesR230Collapse ≡ true
cellRateFunctionAlreadyBuildsSwapInvariantWeight = refl

finitePhysicalDoubleSumSameObjectAlreadyClosed :
  R440.round440R299PhysicalDoubleSumSameObjectIdentificationClosed ≡ true
finitePhysicalDoubleSumSameObjectAlreadyClosed = refl

commonCrossAlreadyIdentifiedWithQuadraticCompanion :
  R440.round440CommonCrossIsR439QuadraticCompanionCross ≡ true
commonCrossAlreadyIdentifiedWithQuadraticCompanion = refl

r299FiniteFactorizationAlreadyClosed :
  R299.round299FinitePairFactorizationCompilerClosed ≡ true
r299FiniteFactorizationAlreadyClosed =
  R299.round299FinitePairFactorizationCompilerClosedIsTrue

r488LocalPaymentFamilyIsParentLeaf :
  R488.firstR423ProducerResidual R488.currentProducerStatus
  ≡ R488.missingFixedOutputPaymentFamily
r488LocalPaymentFamilyIsParentLeaf = R488.currentFirstMissing

r487DirectCompilerAlreadyClosed :
  R487.round487R432ToR423CompilerClosed ≡ true
r487DirectCompilerAlreadyClosed = refl

r423LaplaceRouteIsNotNecessary :
  R423.round423SchurCriticalRouteIsNecessaryProducer ≡ false
r423LaplaceRouteIsNotNecessary =
  R423.round423SchurCriticalRouteIsNecessaryProducerIsFalse

------------------------------------------------------------------------
-- Route dispositions / no-collapse boundaries.
------------------------------------------------------------------------

directSignedPaymentDisposition : Least.RouteDisposition
directSignedPaymentDisposition = Least.admitted

laplaceProducerDisposition : Least.RouteDisposition
laplaceProducerDisposition = Least.admitted

makeLaplaceMandatoryDisposition : Least.RouteDisposition
makeLaplaceMandatoryDisposition = Least.rejected Least.hypothesisInflation

reproveFiniteDoubleSumDisposition : Least.RouteDisposition
reproveFiniteDoubleSumDisposition = Least.redirectedReuse

data OptionalProducerCreatesMandatoryPrerequisite : Set where
data FiniteFactorizationPaysSpacetimeEstimate : Set where

optionalProducerDoesNotCreateMandatoryPrerequisite :
  OptionalProducerCreatesMandatoryPrerequisite → ⊥
optionalProducerDoesNotCreateMandatoryPrerequisite ()

finiteFactorizationDoesNotPaySpacetimeEstimate :
  FiniteFactorizationPaysSpacetimeEstimate → ⊥
finiteFactorizationDoesNotPaySpacetimeEstimate ()

------------------------------------------------------------------------
-- Ledger.
------------------------------------------------------------------------

round489FiniteSameObjectWorkClosed : Bool
round489FiniteSameObjectWorkClosed = true

round489DirectFirstMissingIsSignedSpacetimeEstimate : Bool
round489DirectFirstMissingIsSignedSpacetimeEstimate = true

round489LaplaceAuthorityMandatoryForR423 : Bool
round489LaplaceAuthorityMandatoryForR423 = false

round489LaplaceLaneRemainsOptionalProducer : Bool
round489LaplaceLaneRemainsOptionalProducer = true

round489SignedSpacetimeEstimateClosed : Bool
round489SignedSpacetimeEstimateClosed = false

round489CutoffUniformBudgetSumClosed : Bool
round489CutoffUniformBudgetSumClosed = false

round489R423SignedCompanionBudgetClosed : Bool
round489R423SignedCompanionBudgetClosed = false

round489ClayPromotion : Bool
round489ClayPromotion = false

round489DirectFirstMissingIsSignedSpacetimeEstimateIsTrue :
  round489DirectFirstMissingIsSignedSpacetimeEstimate ≡ true
round489DirectFirstMissingIsSignedSpacetimeEstimateIsTrue = refl

round489LaplaceAuthorityMandatoryForR423IsFalse :
  round489LaplaceAuthorityMandatoryForR423 ≡ false
round489LaplaceAuthorityMandatoryForR423IsFalse = refl

round489SignedSpacetimeEstimateClosedIsFalse :
  round489SignedSpacetimeEstimateClosed ≡ false
round489SignedSpacetimeEstimateClosedIsFalse = refl

round489ClayPromotionIsFalse : round489ClayPromotion ≡ false
round489ClayPromotionIsFalse = refl
