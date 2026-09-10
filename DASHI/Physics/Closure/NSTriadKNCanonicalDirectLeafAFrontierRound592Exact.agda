module DASHI.Physics.Closure.NSTriadKNCanonicalDirectLeafAFrontierRound592Exact where

------------------------------------------------------------------------
-- ROUND592 / CANONICAL LEAF-A FRONTIER = ONE R503 INEQUALITY
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
-- The critical-cone/Bony/Schur and temporal-commutator/FTC constructions remain
-- admissible producer tactics for this inequality, but they are not mandatory
-- prerequisites.  No Laplace realization or full R439 companion is required.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Closure.NSTriadKNDirectResolventPairCompanionRound496Exact as R496
import DASHI.Physics.Closure.NSTriadKNDirectResolventFibreCompanionRound497Exact as R497
import DASHI.Physics.Closure.NSTriadKNDirectResolventGlobalCompanionRound498Exact as R498
import DASHI.Physics.Closure.NSTriadKNDirectResolventTrajectoryCompanionRound499Exact as R499
import DASHI.Physics.Closure.NSTriadKNDirectResolventIntegratedCompanionRound500Exact as R500
import DASHI.Physics.Closure.NSTriadKNDirectResolventSignedCrossToR415Round503Exact as R503
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

round592LaplaceMandatory : Bool
round592LaplaceMandatory = false

round592FullR439CompanionMandatory : Bool
round592FullR439CompanionMandatory = false

round592CriticalConeOrBonyRouteMandatory : Bool
round592CriticalConeOrBonyRouteMandatory = false

round592TemporalCommutatorFTCRouteMandatory : Bool
round592TemporalCommutatorFTCRouteMandatory = false

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

round592LaplaceMandatoryIsFalse : round592LaplaceMandatory ≡ false
round592LaplaceMandatoryIsFalse = refl

round592CriticalConeOrBonyRouteMandatoryIsFalse :
  round592CriticalConeOrBonyRouteMandatory ≡ false
round592CriticalConeOrBonyRouteMandatoryIsFalse = refl

round592TemporalCommutatorFTCRouteMandatoryIsFalse :
  round592TemporalCommutatorFTCRouteMandatory ≡ false
round592TemporalCommutatorFTCRouteMandatoryIsFalse = refl

round592CanonicalLeafAIsSingleDirectOffDiagonalBudgetIsTrue :
  round592CanonicalLeafAIsSingleDirectOffDiagonalBudget ≡ true
round592CanonicalLeafAIsSingleDirectOffDiagonalBudgetIsTrue = refl

round592ClayPromotionIsFalse : round592ClayPromotion ≡ false
round592ClayPromotionIsFalse = refl
