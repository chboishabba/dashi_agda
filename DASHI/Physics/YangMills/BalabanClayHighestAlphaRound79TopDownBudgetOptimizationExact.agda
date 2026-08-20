module DASHI.Physics.YangMills.BalabanClayHighestAlphaRound79TopDownBudgetOptimizationExact where

------------------------------------------------------------------------
-- ROUND79: KEEP THE THREE CLAY-LEVEL THEOREMS, REMOVE ARTIFICIAL NUMERICAL PAIN
--
-- Round78 established the top-down analytic frontier:
--
--   A. UVToContinuumYM
--   B. SameHamiltonianPhysicalMassGap
--   C. SameFamilyLocalFieldsOPEStressWard
--
-- This round does NOT manufacture a fake 3 -> 2 decrement.  Instead it attacks
-- A at the point where earlier bottom-up bookkeeping had frozen convenient
-- constants into apparent research targets.  Three such targets are now
-- theorem-exactly relaxed.
--
-- (1) COERCIVITY
--     Existing reference floor: 1/16.
--     Old split: physical 1/32 + remainder 1/32.
--     Top-down admissible split: physical 1/64 + remainder 3/64.
--     Therefore the signed-remainder allowance and current linear-radius
--     arithmetic increase by exactly 3/2 while a positive physical floor
--     remains.
--
-- (2) ONE-LOOP / BETA
--     The universal SU(2) inverse-coupling coefficient is already exactly
--     11/12.  Hence the regular remainder only needs |r_n| <= R with R<11/12
--     to give a uniformly positive source beta.  R=1/2 is one deliberately
--     wide candidate, yielding beta in [5/12,17/12].
--
--     More importantly, this statement is now lifted to arbitrary compact
--     simple G: b_G=C_A(G)*11/24, and any regular radius R_G<b_G gives the
--     source UniformBetaEnclosure once the literal colour factorization and
--     C_A>0 are supplied.
--
-- (3) ONE-STEP CONTRACTION
--     Old sufficient budget: q_small<=1/2, q_large<=1/32 -> 17/32.
--     Clay-facing need: q_total<1 in ONE corrected norm.
--     Keeping q_small<=1/2, it is enough that q_large<1/2.
--     Thus the old 1/32 large-polymer target was sixteen times smaller than the
--     simple complementary boundary.  More generally any caps s+l<1 suffice.
--
-- These are real analytic simplifications.  They do not prove the remaining
-- physical estimates: source-native selected-background estimates must still
-- hold on the chosen region; the literal Wilson/FP/Haar remainder must still be
-- enclosed; and the small/large costs must be estimates in the SAME corrected
-- norm.  But future analysis should target these weakest sufficient regions,
-- not the historical constants unless extra headroom is genuinely consumed.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayHighestAlphaRound78TopDownThreeAnalyticFrontierExact
import DASHI.Physics.YangMills.BalabanTopDownPositiveCoercivityBudgetExact
import DASHI.Physics.YangMills.BalabanTopDownOneLoopRemainderBudgetExact
import DASHI.Physics.YangMills.BalabanCompactSimpleOneLoopRemainderBudgetExact
import DASHI.Physics.YangMills.BalabanTopDownStrictContractionBudgetExact

------------------------------------------------------------------------
-- The Clay-level frontier count is intentionally unchanged until A, B or C is
-- PHYSICALLY inhabited.  Numerical target relaxation is progress inside A, not
-- a semantic decrement of the endpoint theorem count.
------------------------------------------------------------------------

round79IndependentClayAnalyticEndpointCount : Nat
round79IndependentClayAnalyticEndpointCount = 3

round79TopDownBudgetOptimizationLevel : ProofLevel
round79TopDownBudgetOptimizationLevel = machineChecked

------------------------------------------------------------------------
-- FIRST PHYSICAL LEAVES AFTER THE RELAXATION
--
-- A1. Select a source-native small-field region and prove the literal
--     Wilson/gauge/KKT/Green estimates there.  The old radius 1/8192 remains a
--     valid conservative choice; the arithmetic permits 3/16384 if all local
--     estimates can be re-established there.  There is no reason to enlarge
--     the region merely for aesthetics.
--
-- A2. Construct the SAME literal Wilson + reduced FP + Haar Ward scalar for
--     arbitrary compact-simple G, prove C_A factorization and C_A>0, and
--     enclose its history-dependent regular remainder in ANY convenient
--     R_G < C_A*11/24.  For SU(2), R=1/2 is already sufficient for positivity.
--
-- A3. Prove one physical one-step estimate in the SAME corrected unified norm.
--     If its small/KP branch is <=1/2, the large branch need only be strictly
--     below 1/2 for contraction.  Optimize the actual proof over the full
--     admissible region s+l<1 rather than insisting on 17/32.
--
-- Once A is inhabited, move top-down to B's weakest uniform physical
-- clustering/gap condition, then C's weakest quantitative OPE/stress/Ward
-- condition.  Nontriviality remains downstream of B+C on the same H.
------------------------------------------------------------------------

round79PhysicalUVToContinuumInstantiationLevel : ProofLevel
round79PhysicalUVToContinuumInstantiationLevel = conditional

round79PhysicalSameHamiltonianGapLevel : ProofLevel
round79PhysicalSameHamiltonianGapLevel = conditional

round79PhysicalSameFamilyLocalFieldsLevel : ProofLevel
round79PhysicalSameFamilyLocalFieldsLevel = conditional
