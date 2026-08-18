module DASHI.Physics.YangMills.BalabanClayHighestAlphaRound61DLRTransferAuditValidation where

------------------------------------------------------------------------
-- ROUND61 HIGHEST-ALPHA VALIDATION ROOT
--
-- This tranche does theorem-level work rather than adding new closure receipts.
--
-- (1) ADVERSARIAL DLR SOURCE AUDIT
--
-- Lluis Eriksson,
-- "DLR-Uniform Log-Sobolev Inequality and Unconditional Mass Gap for
-- Lattice Yang--Mills at Weak Coupling", v1, February 2026,
-- ai.viXra:2602.0053v1. No DOI assigned.
--
-- The July 2026 v2 replacement explicitly withdraws the unconditional v1
-- claim and presents a conditional/windowed reduction. Round61 therefore does
-- NOT import v1 as a mass-gap theorem. It proves the exact beta dependence of
-- the displayed v1 fibre-oscillation majorant C_fib = 2 beta n + c.
--
-- (2) REPLACE BOOLEAN W5 BY AN ACTUAL TRANSFER EQUATION
--
-- The theorem-bearing object is B (T_coarse f) = T_fine (B f). Transfer
-- intertwiners compose exactly, so finite-depth compatibility is algebraic once
-- the literal one-step Bałaban/Wilson equation is proved.
--
-- (3) FACTOR THE SOURCE-FACING TRANSFER PROOF INTO TWO COMMUTING SQUARES
--
-- Writing T = trace o kernel, prove on the SAME physical maps
--
--     B_K K_c = K_f B
--     B Tr_c  = Tr_f B_K.
--
-- The old W1'/W2'/W3' obligations feed kernel naturality; W4' is the actual
-- temporal trace/integration interchange law.
--
-- (4) CLOSE THE REDUCED FLAT FP KERNEL AND CONSTRUCT THE EXACT BASE INVERSE
--
-- The computed side-four scalar Green kernel is a two-sided inverse for
-- L + global-average. Since the literal flat FP operator is exactly L in each
-- colour coordinate, L f = 0 forces f to be constant. The anchored
-- representative vanishes at its anchor, so the reduced kernel is trivial.
--
-- Periodic reindexing also proves the flat FP image has colourwise zero site
-- mean. On that source carrier the explicit map source -> anchor (G source) is
-- a right inverse; conversely G(L f)=f-mean(f), so re-anchoring cancels the
-- mean and gives a left inverse on anchored parameters. Thus the reduced flat
-- FP operator is explicitly isomorphic between anchored gauge parameters and
-- colourwise mean-zero ghost sources.
--
-- The flat M0^{-1} required by the background determinant/log-det expansion
-- is therefore concrete and two-sided rather than existential.
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
-- A DirectTransferSchurGapStep evaluates the fine/coarse gap functionals on
-- the exact operators in the TransferIntertwiner before consuming the existing
-- split-loss estimate. Schur scalars therefore cannot float free of the named
-- physical transfer maps.
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
import DASHI.Physics.YangMills.BalabanReducedFlatFaddeevPopovGreenInverseExact
import DASHI.Physics.YangMills.BalabanReducedFlatFaddeevPopovIsomorphismExact
