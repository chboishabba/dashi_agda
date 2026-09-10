module DASHI.Physics.Closure.NSTriadKNCanonicalDirectLeafAFrontierRound592Exact where

------------------------------------------------------------------------
-- ROUND592 / CANONICAL LEAF-A FRONTIER = ONE R503 INEQUALITY
--
-- Introspective correction after R590/R591:
--
-- * R284/R434/R590 critical-cone decomposition is an OPTIONAL producer tactic.
-- * R568/R572 commutator + diagonal temporal reduction is an OPTIONAL producer
--   tactic for R503, useful when its favourable signs make the estimate easier.
-- * Neither tactic is a prerequisite of the canonical Clay-facing leaf.
--
-- R496-R500 already construct the exact live off-diagonal nonseparable
-- resolvent companion and prove
--
--   integral(R406 remainder) = 4 * integratedDirectCompanion.
--
-- R503 then says the only analytic content of leaf A is literally
--
--   4 * integratedDirectCompanion(N,T) <= B(T)
--
-- with B independent of N.
--
-- No Laplace realization, R439 full companion, R284 partition, scalar FTC,
-- self-flux endpoint, Schur estimate, or Bony class norm is mandatory.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Closure.NSTriadKNDirectResolventPairCompanionRound496Exact as R496
import DASHI.Physics.Closure.NSTriadKNDirectResolventFibreCompanionRound497Exact as R497
import DASHI.Physics.Closure.NSTriadKNDirectResolventGlobalCompanionRound498Exact as R498
import DASHI.Physics.Closure.NSTriadKNDirectResolventTrajectoryCompanionRound499Exact as R499
import DASHI.Physics.Closure.NSTriadKNDirectResolventIntegratedCompanionRound500Exact as R500
import DASHI.Physics.Closure.NSTriadKNDirectResolventSignedCrossToR415Round503Exact as R503
import DASHI.Physics.Closure.NSTriadKNCanonicalClayProofSearchRound486Exact as R486
import DASHI.Physics.Closure.NSTriadKNDirectSignedCompanionFrontierRound442Exact as R442
import DASHI.Physics.Closure.NSTriadKNLiveCommutatorOnlyLeafABoundaryRound568Exact as R568
import DASHI.Physics.Closure.NSTriadKNDirectLeafACompilerRound572Exact as R572
import DASHI.Physics.Closure.NSTriadKNLiveCriticalConeRegionPaymentRound590Exact as R590
import DASHI.Physics.Closure.NSTriadKNDirectLeafALeastPrivilegeRound591Exact as R591
import DASHI.Physics.Closure.NSTriadKNLiteralR406ClayTerminalCutsetRound504Exact as R504

round592PairSameObjectClosed : Bool
round592PairSameObjectClosed = R496.round496PairRemainderIsFourDirectCompanionClosed

round592FibreAggregationClosed : Bool
round592FibreAggregationClosed = R497.round497FiniteFibreRemainderIsFourDirectCompanionClosed

round592GlobalAggregationClosed : Bool
round592GlobalAggregationClosed = R498.round498GlobalInstantaneousRemainderIsFourCompanionClosed

round592TrajectorySpecializationClosed : Bool
round592TrajectorySpecializationClosed = R499.round499LiteralR406SliceSpecializationClosed

round592IntegrationSameObjectClosedModuloStandardAuthority : Bool
round592IntegrationSameObjectClosedModuloStandardAuthority =
  R500.round500IntegratedDirectCompanionWeldClosedModuloIntegrationAuthority

round592R503CompilerClosed : Bool
round592R503CompilerClosed = R503.round503ExactR500ToR415CompilerClosed

round592HistoricalR442LaplaceCoordinateStillMandatory : Bool
round592HistoricalR442LaplaceCoordinateStillMandatory = false

round592R284CriticalConeMandatory : Bool
round592R284CriticalConeMandatory = false

round592R568CommutatorTemporalRouteMandatory : Bool
round592R568CommutatorTemporalRouteMandatory = false

round592R572ScalarFTCMandatory : Bool
round592R572ScalarFTCMandatory = false

round592R590LiveRegionPaymentMandatory : Bool
round592R590LiveRegionPaymentMandatory = false

round592R591LeastPrivilegeTemporalProducerMandatory : Bool
round592R591LeastPrivilegeTemporalProducerMandatory = false

round592CanonicalLeafAIsSingleDirectOffDiagonalBudget : Bool
round592CanonicalLeafAIsSingleDirectOffDiagonalBudget = true

round592CanonicalLeafAClosed : Bool
round592CanonicalLeafAClosed = R503.round503DirectOffDiagonalBudgetClosed

round592CurrentGlobalFirstResidualStillLeafA :
  R504.firstTerminalResidual R504.currentTerminalStatus
  ≡ R504.missingLiteralR406SignedCrossPayment
round592CurrentGlobalFirstResidualStillLeafA = R504.currentFirstTerminalResidual

round592ClayPromotion : Bool
round592ClayPromotion = false

round592HistoricalR442LaplaceCoordinateStillMandatoryIsFalse :
  round592HistoricalR442LaplaceCoordinateStillMandatory ≡ false
round592HistoricalR442LaplaceCoordinateStillMandatoryIsFalse = refl

round592R284CriticalConeMandatoryIsFalse :
  round592R284CriticalConeMandatory ≡ false
round592R284CriticalConeMandatoryIsFalse = refl

round592R568CommutatorTemporalRouteMandatoryIsFalse :
  round592R568CommutatorTemporalRouteMandatory ≡ false
round592R568CommutatorTemporalRouteMandatoryIsFalse = refl

round592R572ScalarFTCMandatoryIsFalse :
  round592R572ScalarFTCMandatory ≡ false
round592R572ScalarFTCMandatoryIsFalse = refl

round592CanonicalLeafAIsSingleDirectOffDiagonalBudgetIsTrue :
  round592CanonicalLeafAIsSingleDirectOffDiagonalBudget ≡ true
round592CanonicalLeafAIsSingleDirectOffDiagonalBudgetIsTrue = refl

round592ClayPromotionIsFalse : round592ClayPromotion ≡ false
round592ClayPromotionIsFalse = refl
