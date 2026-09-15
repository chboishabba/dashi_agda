module DASHI.Governance.GovernanceConsumerSafeParetoValidation where

import DASHI.Core.ConsumerSafeRefinementPromotionExact as Static
import DASHI.Core.ConsumerSafeFuturePromotionExact as Future
import DASHI.Governance.ConsumerSafeGovernancePromotionExact as Governance
import DASHI.Governance.ResidualIndexedEvidenceSchedulerExact as Scheduler
import DASHI.Governance.GovernanceRoleParetoSymmetryExact as Symmetry

------------------------------------------------------------------------
-- RED-first tranche contract.
--
-- This validation root deliberately names the future production owners before
-- they exist on this branch.  The production tranche must expose the canonical
-- generic promotion layers plus the three governance specialisations below.
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
