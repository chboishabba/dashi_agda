module DASHI.Physics.Closure.NSTriadKNStrictR423ProofSearchRound493Exact where

------------------------------------------------------------------------
-- ROUND493 / STRICT R423 FIRST-MISSING SEARCH AFTER SAME-OBJECT AUDIT
--
-- R494 closes the instantaneous normalization
--
--   2 * C_k = literal R439 quadratic-companion cross.
--
-- But the physical dynamics exposes only an abstract
--
--   integrateTo : (Time -> Q) -> Time -> Q,
--
-- whose type contains no congruence or finite-additivity laws.  R495 therefore
-- isolates those standard integration transport laws as an explicit authority.
-- The strict Clay-facing sufficient route is now:
--
--   S0. integration transport authority;
--   S1. integrated R299-normalized companion same-object weld;
--   S2. same-output/same-scale signed spacetime estimate;
--   S3. cutoff-uniform sum of fibre budgets.
--
-- R490/R491 Laplace realization remains an optional producer strategy, not a
-- mandatory prerequisite of R423.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Core.ProofSearchLeastPrivilegeAdmissionExact as Least
import DASHI.Physics.Closure.NSTriadKNR423LocalPaymentPrerequisiteRound489Exact as R489
import DASHI.Physics.Closure.NSTriadKNPositiveRateLaplaceAuthorityRound490Exact as R490
import DASHI.Physics.Closure.NSTriadKNPhysicalCauchyLaplaceWeldRound491Exact as R491
import DASHI.Physics.Closure.NSTriadKNStrictFixedOutputCompanionToR423Round492Exact as R492
import DASHI.Physics.Closure.NSTriadKNR299NormalizedCompanionSameObjectRound494Exact as R494
import DASHI.Physics.Closure.NSTriadKNIntegrationTransportAuthorityRound495Exact as R495

------------------------------------------------------------------------
-- First-missing strict route.
------------------------------------------------------------------------

data StrictResidual : Set where
  missingIntegrationTransportAuthority : StrictResidual
  missingLiteralIntegratedCompanionWeld : StrictResidual
  missingSignedSpacetimeEstimate : StrictResidual
  missingCutoffUniformBudgetSum : StrictResidual
  strictR423ProducerClosed : StrictResidual

record StrictStatus : Set where
  constructor strict-status
  field
    integrationTransportPresent : Bool
    companionWeldPresent : Bool
    signedEstimatePresent : Bool
    budgetSumPresent : Bool

open StrictStatus public

firstStrictResidual : StrictStatus → StrictResidual
firstStrictResidual (strict-status false weld estimate budget) =
  missingIntegrationTransportAuthority
firstStrictResidual (strict-status true false estimate budget) =
  missingLiteralIntegratedCompanionWeld
firstStrictResidual (strict-status true true false budget) =
  missingSignedSpacetimeEstimate
firstStrictResidual (strict-status true true true false) =
  missingCutoffUniformBudgetSum
firstStrictResidual (strict-status true true true true) =
  strictR423ProducerClosed

data StrictMechanism : Set where
  LookIntegrationTransportAuthority : StrictMechanism
  LookSameObjectTrajectoryCompanionWeld : StrictMechanism
  ThinkSameScaleSignedSpacetime : StrictMechanism
  ThinkCutoffUniformBudgetAggregation : StrictMechanism
  CompileStrictR492ToR423 : StrictMechanism

mechanismFor : StrictResidual → StrictMechanism
mechanismFor missingIntegrationTransportAuthority =
  LookIntegrationTransportAuthority
mechanismFor missingLiteralIntegratedCompanionWeld =
  LookSameObjectTrajectoryCompanionWeld
mechanismFor missingSignedSpacetimeEstimate = ThinkSameScaleSignedSpacetime
mechanismFor missingCutoffUniformBudgetSum = ThinkCutoffUniformBudgetAggregation
mechanismFor strictR423ProducerClosed = CompileStrictR492ToR423

currentStrictStatus : StrictStatus
currentStrictStatus = strict-status false false false false

currentFirstStrictResidual :
  firstStrictResidual currentStrictStatus
  ≡ missingIntegrationTransportAuthority
currentFirstStrictResidual = refl

currentStrictMechanism :
  mechanismFor (firstStrictResidual currentStrictStatus)
  ≡ LookIntegrationTransportAuthority
currentStrictMechanism = refl

afterIntegrationTransportStatus : StrictStatus
afterIntegrationTransportStatus = strict-status true false false false

afterIntegrationTransportFirstResidual :
  firstStrictResidual afterIntegrationTransportStatus
  ≡ missingLiteralIntegratedCompanionWeld
afterIntegrationTransportFirstResidual = refl

afterCompanionWeldStatus : StrictStatus
afterCompanionWeldStatus = strict-status true true false false

afterCompanionWeldFirstResidual :
  firstStrictResidual afterCompanionWeldStatus
  ≡ missingSignedSpacetimeEstimate
afterCompanionWeldFirstResidual = refl

------------------------------------------------------------------------
-- Route classifications and exact pins.
------------------------------------------------------------------------

strictR492Disposition : Least.RouteDisposition
strictR492Disposition = Least.admitted

integrationTransportDisposition : Least.RouteDisposition
integrationTransportDisposition = Least.admitted

laplaceProducerDisposition : Least.RouteDisposition
laplaceProducerDisposition = Least.admitted

laplaceAsMandatoryDisposition : Least.RouteDisposition
laplaceAsMandatoryDisposition = Least.rejected Least.hypothesisInflation

estimateBeforeCompanionWeldDisposition : Least.RouteDisposition
estimateBeforeCompanionWeldDisposition =
  Least.rejected Least.missingPrerequisite

r489DirectEstimateRemainsPhysicalLeafAfterWeld :
  R489.round489DirectFirstMissingIsSignedSpacetimeEstimate ≡ true
r489DirectEstimateRemainsPhysicalLeafAfterWeld = refl

r492SameObjectReceiptIsRequired :
  R492.round492ExternalSameObjectCompanionReceiptRequired ≡ true
r492SameObjectReceiptIsRequired = refl

r494InstantaneousNormalizationClosed :
  R494.round494R299NormalizationToLiteralCompanionClosed ≡ true
r494InstantaneousNormalizationClosed =
  R494.round494R299NormalizationToLiteralCompanionClosedIsTrue

r495BareIntegrateToHasNoTransportReceipt :
  R495.round495BareIntegrateToTypeSuppliesTransportLaws ≡ false
r495BareIntegrateToHasNoTransportReceipt =
  R495.round495BareIntegrateToTypeSuppliesTransportLawsIsFalse

r490AuthorityInterfaceDoesNotCreateInhabitant :
  R490.round490AuthorityInterfaceCreatesAuthorityInhabitant ≡ false
r490AuthorityInterfaceDoesNotCreateInhabitant = refl

r491PhysicalKernelSpecializationNeedsNoNewNSIdentity :
  R491.round491PhysicalCellLaplaceWeldNeedsNoNewNSIdentity ≡ true
r491PhysicalKernelSpecializationNeedsNoNewNSIdentity =
  R491.round491PhysicalCellLaplaceWeldNeedsNoNewNSIdentityIsTrue

data ScalarBudgetWithoutCompanionIdentityPaysR423 : Set where

scalarBudgetCannotReplaceCompanionIdentity :
  ScalarBudgetWithoutCompanionIdentityPaysR423 → ⊥
scalarBudgetCannotReplaceCompanionIdentity ()

------------------------------------------------------------------------
-- Ledger.
------------------------------------------------------------------------

round493FirstMissingIsIntegrationTransportAuthority : Bool
round493FirstMissingIsIntegrationTransportAuthority = true

round493InstantaneousCompanionNormalizationClosed : Bool
round493InstantaneousCompanionNormalizationClosed = true

round493LaplaceMandatory : Bool
round493LaplaceMandatory = false

round493IntegrationTransportAuthorityClosed : Bool
round493IntegrationTransportAuthorityClosed = false

round493CompanionWeldClosed : Bool
round493CompanionWeldClosed = false

round493SignedSpacetimeEstimateClosed : Bool
round493SignedSpacetimeEstimateClosed = false

round493CutoffUniformBudgetSumClosed : Bool
round493CutoffUniformBudgetSumClosed = false

round493StrictR423ProducerClosed : Bool
round493StrictR423ProducerClosed = false

round493ClayPromotion : Bool
round493ClayPromotion = false

round493FirstMissingIsIntegrationTransportAuthorityIsTrue :
  round493FirstMissingIsIntegrationTransportAuthority ≡ true
round493FirstMissingIsIntegrationTransportAuthorityIsTrue = refl

round493LaplaceMandatoryIsFalse : round493LaplaceMandatory ≡ false
round493LaplaceMandatoryIsFalse = refl

round493ClayPromotionIsFalse : round493ClayPromotion ≡ false
round493ClayPromotionIsFalse = refl
