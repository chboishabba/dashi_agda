module DASHI.Physics.YangMills.BalabanClayHighestAlphaRound80SevenAnalyticLeafAttackExact where

------------------------------------------------------------------------
-- ROUND80: SEVEN ACTUAL ANALYTIC LEAVES, WITH L3 NUMERICS REMOVED
--
-- Round78/79 use three Clay-facing endpoint theorems A/B/C.  For active
-- mathematical work the honest first-analytic-leaf cutset is seven:
--
-- L1 SelectedBackgroundUniformStability
-- L2 LiteralCompactSimplePositiveBeta
-- L3 UnifiedPhysicalRGStep
-- L4 UniformHeatHessianDebt
-- L5 UniformCovariantFiniteSpeed
-- L6 SameFamilyCompositeOPERemainder
-- L7 SameFamilyStressWardHamiltonian
--
-- This round deliberately does NOT decrement seven merely because supporting
-- algebra became easier.  It does, however, remove two artificial parts of L3:
-- the historical numerical target and an independent same-object weld.
--
-- Repository archaeology found the older blocked-L2 WC3 lane recording
-- q=0.23178189475262734 and eta=4 with 4q<1.  Round80 re-encodes q exactly as a
-- rational and proves q<1/4.  Combined with the existing small/KP target <=1/2,
-- the total corrected one-step cost is <3/4 PROVIDED the two physical
-- inequalities hold on the corrected source-native unified state.
--
-- Round76 already made that strong state an extension of the literal
-- CMP119/CMP122 complete density. `BalabanSourceNativeUnifiedThreeQuarterStepExact`
-- now types both costs on the SAME `SourceNativeUnifiedState`, so there is no
-- third cross-carrier equality theorem left to prove.
--
-- Thus the sharp live analytic content of L3 is now only:
--
--   L3a. prove actual source-native unified small/KP cost <= 1/2;
--   L3b. prove actual source-native unified large cost <= blocked-L2 q.
--
-- The exact compiler then supplies q_total<3/4<1.
--
-- DOI / Birman-Solomyak calculus is added as a supporting L6/L7 tool but is
-- explicitly not counted as an OPE or stress-tensor proof.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayHighestAlphaRound79TopDownBudgetOptimizationExact
import DASHI.Physics.YangMills.BalabanBlockedL2LargeBranchQuarterContractionExact
import DASHI.Physics.YangMills.BalabanBlockedL2UnifiedThreeQuarterContractionExact
import DASHI.Physics.YangMills.BalabanSourceNativeUnifiedThreeQuarterStepExact
import DASHI.Physics.YangMills.BirmanSolomyakDoubleOperatorIntegralBoundaryExact

round80ActualAnalyticLeafCount : Nat
round80ActualAnalyticLeafCount = 7

round80L3NumericalOptimizationLevel : ProofLevel
round80L3NumericalOptimizationLevel = machineChecked

round80L3SameObjectTypingLevel : ProofLevel
round80L3SameObjectTypingLevel = machineChecked

------------------------------------------------------------------------
-- Seven-leaf status.  Only a genuine physical inhabitant changes the count.
------------------------------------------------------------------------

l1SelectedBackgroundUniformStabilityLevel : ProofLevel
l1SelectedBackgroundUniformStabilityLevel = conditional

l2LiteralCompactSimplePositiveBetaLevel : ProofLevel
l2LiteralCompactSimplePositiveBetaLevel = conditional

l3UnifiedPhysicalRGStepLevel : ProofLevel
l3UnifiedPhysicalRGStepLevel = conditional

l4UniformHeatHessianDebtLevel : ProofLevel
l4UniformHeatHessianDebtLevel = conditional

l5UniformCovariantFiniteSpeedLevel : ProofLevel
l5UniformCovariantFiniteSpeedLevel = conditional

l6SameFamilyCompositeOPERemainderLevel : ProofLevel
l6SameFamilyCompositeOPERemainderLevel = conditional

l7SameFamilyStressWardHamiltonianLevel : ProofLevel
l7SameFamilyStressWardHamiltonianLevel = conditional

------------------------------------------------------------------------
-- NEXT PHYSICAL TARGET
--
-- Attack L3b by proving that the large-polymer coordinate OF THE SAME
-- source-native unified state is dominated by the blocked-L2 physical activity
-- whose older WC3 analysis produced q.  There is no longer an independent
-- source/repository state equality theorem.  Once L3b lands, only L3a remains
-- before the exact <3/4 compiler fires and L3 itself is closed.
------------------------------------------------------------------------

round80PhysicalUnifiedLargeBlockedL2Level : ProofLevel
round80PhysicalUnifiedLargeBlockedL2Level = conditional

round80PhysicalUnifiedSmallHalfLevel : ProofLevel
round80PhysicalUnifiedSmallHalfLevel = conditional
