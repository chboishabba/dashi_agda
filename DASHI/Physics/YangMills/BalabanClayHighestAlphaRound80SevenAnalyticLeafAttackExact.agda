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
-- algebra became easier.  It does, however, remove the historical numerical
-- difficulty from the large-polymer side of L3.
--
-- Repository archaeology found the older blocked-L2 WC3 lane recording
-- q=0.23178189475262734 and eta=4 with 4q<1.  Round80 re-encodes q exactly as a
-- rational and proves q<1/4.  Combined with the existing small/KP target <=1/2,
-- the total corrected one-step cost is <3/4 PROVIDED both estimates are on the
-- SAME source-native unified norm.
--
-- Thus L3 is no longer an exercise in proving 1/32 or 17/32.  Its sharp live
-- analytic content is now:
--
--   L3a. prove actual corrected unified small/KP cost <= 1/2;
--   L3b. prove actual corrected unified large cost <= blocked-L2 q;
--   L3c. verify both are coordinates of the SAME source-native state/norm.
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
import DASHI.Physics.YangMills.BirmanSolomyakDoubleOperatorIntegralBoundaryExact

round80ActualAnalyticLeafCount : Nat
round80ActualAnalyticLeafCount = 7

round80L3NumericalOptimizationLevel : ProofLevel
round80L3NumericalOptimizationLevel = machineChecked

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
-- Attack L3b by proving that the actual source-native large-polymer coordinate
-- of the corrected unified norm is dominated by the blocked-L2 physical
-- activity whose old WC3 analysis produced q.  This must be a same-object
-- theorem, not equality of two numerical labels.  If it lands, L3 retains only
-- the small/KP same-norm estimate and common-coordinate weld before the exact
-- <3/4 compiler fires.
------------------------------------------------------------------------

round80PhysicalBlockedL2SameObjectWeldLevel : ProofLevel
round80PhysicalBlockedL2SameObjectWeldLevel = conditional
