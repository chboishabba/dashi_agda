module DASHI.Physics.YangMills.BalabanClayHighestAlphaRound61DLRTransferAuditValidation where

------------------------------------------------------------------------
-- ROUND61 HIGHEST-ALPHA VALIDATION ROOT
--
-- This tranche does four theorem-level things rather than adding new closure
-- receipts.
--
-- (1) ADVERSARIAL DLR SOURCE AUDIT
--
-- Lluis Eriksson,
-- "DLR-Uniform Log-Sobolev Inequality and Unconditional Mass Gap for
-- Lattice Yang--Mills at Weak Coupling", v1, February 2026,
-- ai.viXra:2602.0053v1. No DOI assigned.
--
-- The July 2026 v2 replacement explicitly withdraws the unconditional v1
-- claim and presents a conditional/windowed reduction.  Round61 therefore
-- does NOT import v1 as a mass-gap theorem.  It salvages only the local frozen-
-- boundary/fibre observations and proves the exact beta dependence of v1's
-- displayed oscillation majorant
--
--     C_fib(beta,n,c) = 2 beta n + c.
--
-- In particular, boundary-uniformity is not beta-uniformity.
--
-- (2) REPLACE BOOLEAN W5 BY AN ACTUAL TRANSFER EQUATION
--
-- The historical W1--W5 lane records compatibility with Bool fields.  The new
-- theorem-bearing object is
--
--     B (T_coarse f) = T_fine (B f).
--
-- Transfer intertwiners compose exactly, so once one literal Bałaban/Wilson
-- equation is proved per RG step, arbitrary finite-depth compatibility is
-- algebraic rather than a fresh physical assumption.
--
-- (3) FACTOR THE SOURCE-FACING TRANSFER PROOF INTO TWO COMMUTING SQUARES
--
-- Writing T = trace o kernel, it is enough to prove on the SAME physical maps
--
--     B_K K_c = K_f B
--
-- and
--
--     B Tr_c = Tr_f B_K.
--
-- The old W1'/W2'/W3' physical obligations feed kernel naturality; W4' is the
-- actual temporal trace/integration interchange law.  This is the precise
-- target for any source-native Bałaban transfer calculation.
--
-- (4) CLOSE THE REDUCED FLAT FP KERNEL THEOREM
--
-- The existing computed side-four scalar Green kernel is a two-sided inverse
-- for L + global-average.  Since the literal flat FP operator is exactly L in
-- each colour coordinate, L f = 0 forces f to be constant.  The anchored
-- representative vanishes at its anchor, so the reduced kernel is trivial.
--
-- Hence the former B1 item
--
--     ReducedFlatFaddeevPopovKernelIsOnlyGlobalGauge
--
-- is now machine-checked on the actual finite physical carrier.  The next
-- ghost theorem is the reduced determinant/log-det background expansion.
--
-- (5) WELD FESHBACH/SCHUR BOOKKEEPING TO THE NAMED TRANSFER OPERATORS
--
-- Volker Bach, Juerg Froehlich and Israel Michael Sigal,
-- "Renormalization Group Analysis of Spectral Problems in Quantum Field
-- Theory", Advances in Mathematics 137 (1998), 205--298.
-- DOI: 10.1006/aima.1998.1733.
--
-- Volker Bach, Thomas Chen, Juerg Froehlich and Israel Michael Sigal,
-- "Smooth Feshbach Map and Operator-Theoretic Renormalization Group
-- Methods", JFA 203 (2003), 44--92.
-- DOI: 10.1016/S0022-1236(03)00057-0.
--
-- Round61 prevents the Schur gap scalars from floating free of the transfer
-- maps: a DirectTransferSchurGapStep evaluates the fine/coarse gap functionals
-- on the exact operators in the TransferIntertwiner before consuming the
-- existing split-loss estimate.
--
-- REMAINING DIRECT-TRANSFER FRONTIER
--
--   literal Bałaban kernel naturality on the Wilson transfer carrier;
--   literal temporal trace/integration naturality;
--   terminal physical transfer spectral gap;
--   cutoff-uniform physical Schur/remainder loss estimates and strict budget.
--
-- Luescher strict positivity is NOT a mass gap, and Eriksson v1 is NOT used to
-- fill any of these hypotheses.
------------------------------------------------------------------------

import DASHI.Physics.YangMills.BalabanClayHighestAlphaRound60WilsonRPG2Validation

import DASHI.Physics.YangMills.BalabanErikssonDLRUniformityAuditExact
import DASHI.Physics.YangMills.BalabanWilsonTransferIntertwinerExact
import DASHI.Physics.YangMills.BalabanTransferKernelTraceNaturalityExact
import DASHI.Physics.YangMills.BalabanDirectTransferSchurGapWeldExact
import DASHI.Physics.YangMills.BalabanReducedFlatFaddeevPopovKernelExact
