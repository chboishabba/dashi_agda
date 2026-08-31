module DASHI.Physics.YangMills.BalabanRowARecentLeanCrossProverProgressExact where

------------------------------------------------------------------------
-- ROW A / ROW B RECENT LEAN CROSS-PROVER SYNCHRONIZATION (2026-08-29)
--
-- This module records the newest machine-checked Lean progress without
-- promoting it to Agda theorem authority.  The frozen research scoreboard
-- therefore remains four until one literal physical completion row is
-- inhabited in Agda (or an accepted cross-prover import policy is added).
--
-- PRIMARY SOURCES VERIFIED IN THE PARALLEL LEAN LANE
--
-- Tadeusz Bałaban,
-- "Averaging Operations for Lattice Gauge Theories",
-- Communications in Mathematical Physics 98 (1985), 17--51.
-- DOI: 10.1007/BF01211042.
--
-- Tadeusz Bałaban,
-- "Propagators for Lattice Gauge Theories in a Background Field",
-- Communications in Mathematical Physics 99 (1985), 389--434.
-- DOI: 10.1007/BF01240355.
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I.",
-- Communications in Mathematical Physics 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223.
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. II.
-- Cluster Expansions", Communications in Mathematical Physics 116 (1988),
-- 1--22. DOI: 10.1007/BF01239022.
--
-- SOURCE-PACK CORRECTIONS CONFIRMED BY DIRECT READING
--
-- * CMP98 Eq. (124) is the full one-step linear averaging form; Eq. (125) is
--   the flat/main term.  Proposition 3 supplies the linear estimate and
--   Proposition 7 joint analyticity.  The source leaves the analytic radius
--   and O(1) constants existentially "sufficiently small" rather than printing
--   numerical constants.
--
-- * CMP109 Eq. (5.1) defines the polarization tensor by a second variation and
--   Eqs. (5.36)--(5.41) fix the tensor-structure normalization.  The parallel
--   Lean lane proves the mixed off-diagonal extraction identity
--
--       beta = - d_mu d_nu Pi_mu_nu |_(p=0),   mu /= nu.
--
-- * CMP109 Theorem 1 is conditional on the effective-coupling trajectory
--   staying in the small-field interval.  Theorem 2 states the tuned SU(2)
--   trajectory/two-sided bounds but defers its proof to a separate publication.
--   Hence the Row-A tuned-trajectory step is genuine mathematics, not merely a
--   transcription task.
--
-- CURRENT LEAN ROW-A STATE
--
-- The parallel Lean lane now proves, with no sorry/new axiom/unsafe:
--
--   (A1 source/gaussian)
--   * literal-shaped CMP98 Eq. (125) averaging equals the project's block
--     averaging operator;
--   * constant reproduction implies derivative-kernel total mass zero;
--   * the derivative kernel has an explicit linear-vanishing bound;
--   * the eliminated-coordinate derivative is the pivot solve
--         E (- P^-1 Q' C)
--     with explicit entrywise constants;
--   * Ward-transverse Gaussian floor and free/interacting integrability;
--   * CMP109 polarization tensor normalization is welded to the shell
--     coefficient convention;
--   * five quartic channels are assigned to explicit polynomial/Cauchy/log
--     remainder interfaces and give a finite C_beta;
--   * the resulting source-facing shell coefficient has a uniform positive
--     lower bound in the Lean normalization.
--
--   (A-i terminal bilateral tube)
--   * the additive quartic defect is removed either by a uniform smallness
--     condition or on sufficiently late terminal blocks;
--   * the source-required terminal tails have strict positive lower slope and
--     finite upper slope.
--
--   (A-ii shooting algebra)
--   * a q-Lipschitz cumulative beta map with q<1 gives the shooting contraction
--     and the unique tuned bare coupling hitting the prescribed observation
--     scale while staying in the small-field window;
--   * geometric history-response decay plus summable shell sensitivity imply a
--     cutoff-uniform cumulative sensitivity bound.
--
-- Therefore the first remaining Row-A physical estimate is now sharp:
--
--     prove, on the literal Wilson / reduced-FP / Haar trajectory,
--
--       |B_K(u) - B_K(v)| <= q |u-v|     with q < 1,
--
--     in the inverse-square coupling coordinate u = g^-2.
--
-- The preferred attack is to split the explicit marginal coupling coordinate
-- from contracting irrelevant history, differentiate the literal beta map in
-- u, retain the g_j powers supplied by the quartic/Cauchy source majorants, and
-- sum them using the already-proved trajectory bounds.  No artificial
-- exponential forgetting is to be assigned to the marginal coupling.
--
-- CURRENT LEAN ROW-B STATE
--
-- The scalar shell-energy summation theorem is also already proved in Lean:
-- an activity majorant exp(-mu n) and entropy bound exp(nu n), with nu < mu,
-- give
--
--       E_n <= A B r^n,       r = exp(nu-mu) < 1,
--
-- and a summable total shell energy.  Thus the Row-B physical seam is now the
-- literal CMP116 marked/polymer activity decay and entropy constants, not the
-- geometric-series algebra.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Cross-prover status surfaces: intentionally conditional in Agda
------------------------------------------------------------------------

rowASourcePackVerificationCrossProverLevel : ProofLevel
rowASourcePackVerificationCrossProverLevel = conditional

rowALiteralAveragingAndPivotWeldCrossProverLevel : ProofLevel
rowALiteralAveragingAndPivotWeldCrossProverLevel = conditional

rowAPolarizationTensorNormalizationCrossProverLevel : ProofLevel
rowAPolarizationTensorNormalizationCrossProverLevel = conditional

rowAFiveChannelMajorantCrossProverLevel : ProofLevel
rowAFiveChannelMajorantCrossProverLevel = conditional

rowATerminalBilateralTubeCrossProverLevel : ProofLevel
rowATerminalBilateralTubeCrossProverLevel = conditional

rowAShootingCompilerCrossProverLevel : ProofLevel
rowAShootingCompilerCrossProverLevel = conditional

rowASensitivityFromResponseCrossProverLevel : ProofLevel
rowASensitivityFromResponseCrossProverLevel = conditional

-- This is the unique first Row-A physical blocker after the recent Lean round.
literalCumulativeBetaSensitivityQStrictlyBelowOneCurrentLevel : ProofLevel
literalCumulativeBetaSensitivityQStrictlyBelowOneCurrentLevel = conditional

rowBShellEnergyGeometricSummationCrossProverLevel : ProofLevel
rowBShellEnergyGeometricSummationCrossProverLevel = conditional

literalCMP116MarkedActivityDecayCurrentLevel : ProofLevel
literalCMP116MarkedActivityDecayCurrentLevel = conditional

------------------------------------------------------------------------
-- Frozen authority boundary
------------------------------------------------------------------------

recentCrossProverFrozenResearchCount : Nat
recentCrossProverFrozenResearchCount = 4

-- No A/B/C/D row is promoted here merely because the parallel Lean lane built.
rowACompletionAfterRecentCrossProverProgressLevel : ProofLevel
rowACompletionAfterRecentCrossProverProgressLevel = conditional

rowBCompletionAfterRecentCrossProverProgressLevel : ProofLevel
rowBCompletionAfterRecentCrossProverProgressLevel = conditional
