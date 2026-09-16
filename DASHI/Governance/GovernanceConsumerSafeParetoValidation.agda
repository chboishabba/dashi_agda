module DASHI.Governance.GovernanceConsumerSafeParetoValidation where

import DASHI.Core.ConsumerSafeRefinementPromotionExact as Static
import DASHI.Core.ConsumerSafeFuturePromotionExact as Future
import DASHI.Governance.ConsumerSafeGovernancePromotionExact as Governance
import DASHI.Governance.ResidualIndexedEvidenceSchedulerExact as Scheduler
import DASHI.Governance.GovernanceRoleParetoSymmetryExact as Symmetry
import DASHI.Governance.GovernanceRecursiveParetoLiftExact as Recursive

------------------------------------------------------------------------
-- RED-first tranche contract.
--
-- This validation root deliberately names future production owners before they
-- exist.  The production tranche must expose the canonical generic promotion
-- layers, three governance specialisations, and the residual-relevant recursive
-- frontier lift.
------------------------------------------------------------------------

staticPromotionBoundary : Static.ConsumerSafeRefinementPromotionBoundary
staticPromotionBoundary = Static.canonicalConsumerSafeRefinementPromotionBoundary

futurePromotionBoundary : Future.ConsumerSafeFuturePromotionBoundary
futurePromotionBoundary = Future.canonicalConsumerSafeFuturePromotionBoundary

governanceBoundary : Governance.ConsumerSafeGovernancePromotionBoundary
governanceBoundary = Governance.canonicalConsumerSafeGovernancePromotionBoundary

schedulerBoundary : Scheduler.ResidualEvidenceSchedulerBoundary
schedulerBoundary = Scheduler.canonicalResidualEvidenceSchedulerBoundary

symmetryBoundary : Symmetry.GovernanceRoleParetoSymmetryBoundary
symmetryBoundary = Symmetry.canonicalGovernanceRoleParetoSymmetryBoundary

recursiveBoundary : Recursive.GovernanceRecursiveParetoLiftBoundary
recursiveBoundary = Recursive.canonicalGovernanceRecursiveParetoLiftBoundary
