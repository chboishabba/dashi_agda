module DASHI.Physics.YangMills.BalabanClayHighestAlphaRound61DLRTransferAuditValidation where

------------------------------------------------------------------------
-- ROUND61 HIGHEST-ALPHA VALIDATION ROOT
--
-- TRANSFER / SPECTRAL ROUTE
-- * Boolean W1--W5 closure is replaced by B(T_c f)=T_f(B f).
-- * Physical one-step compatibility is factored into kernel and trace squares.
-- * Schur/Feshbach gap bookkeeping consumes those exact named transfer maps.
--
-- REDUCED GHOST ROUTE
-- * flat FP kernel = global colour gauge; anchoring removes it;
-- * M0^{-1} is an explicit two-sided Green inverse on mean-zero sources;
-- * reduced trace carrier is explicit, dimension 765;
-- * R_A=M_A M0^{-1}-I is the literal same-carrier relative operator;
-- * source-native X1,...,X4 are constructed from D_A G_A M0^{-1};
-- * cyclic trace gives the exact noncommutative fourth-order log polynomial;
-- * the actual anchored physical R_A satisfies
--       rowMass(R_A) <= 104601/524288 < 1/5;
-- * every finite degree >=5 matrix-log majorant has row mass <=1/2500;
-- * the ACTUAL alternating signed degree-five tail is now constructed and has
--   the same 1/2500 row cap; cancellation signs therefore cost no extra norm;
-- * shifted tails have the geometric Cauchy modulus
--       rowMass(Tail_m) <= (1/5)^m / 2500 <= (1/2)^m;
-- * the safe redundant trace cost 768 is absorbed by the same fifth-tail factor.
-- Remaining ghost closure is finite same-object prefix/tail splitting followed
-- by standard finite principal-log/determinant functional calculus.  Those are
-- no longer classified as independent physical research producers.
--
-- CMP109 / ONE-LOOP ROUTE
-- * source-radius inverse-dexp coefficient is actual Bishop-real data;
-- * 0 <= beta(1/12)-1/12 <= 1/14400 and symmetric coefficient >=23/24;
-- * J=I+c1 ad_X+beta ad_X^2 is literal Bishop-real operator data;
-- * source Euclidean reflection covariance kills every nontrivial (C2)^4
--   Walsh sector exactly BEFORE interval arithmetic;
-- * permutation covariance then reduces the 240 regular Brillouin cells to
--   four trivial-character representatives with weights 64,96,64,16.
-- Remaining one-loop producer is therefore the same-object Wilson/FP/Haar
-- scalar identification plus the four representative Bishop enclosures and
-- the resulting positive colour/orbit coefficient.
--
-- G2 / KKT ROUTE -- DEGREE-ONE EXACT COLLAPSE
-- * the projected Schur Green preserves the stored mean-zero computational
--   quotient exactly; this is useful for reduced coercivity/locality but is NOT
--   silently identified with the raw background-dependent Moore--Penrose K+;
-- * stabilizer stratification makes a background-uniform raw rowMass(K+) the
--   wrong dependency target because null/rank strata vary;
-- * canonical source/defect subset partials are literal constraint images
--       s_S=L(P_S g), delta_S=L(P_S w);
-- * the KKT repair is an orthogonal projector, giving the rank-independent
--       <L v,K+ L v> = ||L* K+ L v||^2 <= ||v||^2;
-- * the four literal plaquette boundary cells are pairwise distinct;
-- * subset-localization is therefore additive on those four slots:
--       L1=P_p v, L2=3 L1, L3=3 L1, L4=L1;
-- * the exact Rota/Mobius formulas consequently force source and defect
--       D2=D3=D4=0;
-- * hence FIFTEEN of the sixteen canonical Green degree blocks vanish exactly;
--   only G11 can survive;
-- * the remaining Green lower bound costs only
--       1/2 (||g_1||^2 + ||w_1||^2),
--   rather than 2(sum_d ||g_d||^2 + sum_d ||w_d||^2);
-- * the literal defect degree-one state is P_p h and finite incidence gives
--       3 ||w_1||^2 = C_p(h),
--   so the defect charge-relative coefficient is EXACTLY 1/3;
-- * the sharp degree-one compiler is therefore
--       residualRatio = rawTotal + 1/2 (sourceDegreeOneRatio + 1/3).
-- Remaining G2 physical work is only the raw aggregate estimate, the literal
-- Wilson source-degree-one norm/charge estimate on the selected family, and
-- the final rational headroom comparison.  No K+ row bound or LBB constant is
-- on the G2 critical path.
--
-- CONTINUUM ROUTE
-- Krzysztof Gawedzki and Antti Kupiainen,
-- "A Rigorous Block Spin Approach to Massless Lattice Theories",
-- CMP 77 (1980), 31--64. DOI: 10.1007/BF01205038.
--
-- Krzysztof Gawedzki and Antti Kupiainen,
-- "Massless Lattice phi^4_4 Theory: Rigorous Control of a Renormalizable
-- Asymptotically Free Model", CMP 99 (1985), 197--252.
-- DOI: 10.1007/BF01212281.
--
-- * generic Prokhorov extraction is separated from physical tightness;
-- * scale-local RG increments have an exact geometric Cauchy compiler;
-- * one strict gauge-invariant fourth cumulant refutes Gaussian/Wick
--   factorization, without substituting an area-law target.
-- Remaining physical producers: same-observable scale increments, tightness,
-- OS-stable unique continuum limit, fourth-cumulant lower bound, and uniform
-- physical exponential clustering.  Clustering -> Hamiltonian gap is treated
-- downstream as standard OS/spectral closure, not as another YM estimate.
--
-- COMPACT-SIMPLE-G ROUTE
-- * finite trace/Fubini proves dim(R) C_R = dim(g) I_R.
-- Group-specific analytic constants remain open.
--
-- SOURCE DISCIPLINE
-- Tadeusz Balaban, "Large Field Renormalization I: The Basic Step of the
-- R-Operation", CMP 122 (1989), 175--202. DOI: 10.1007/BF01257412.
-- CMP119/CMP122 Theorem 1 retains its small-running-coupling hypothesis; the
-- author's unpublished second-order theorem is not fabricated.
--
-- REMAINING DIRECT-TRANSFER FRONTIER
--   literal Balaban kernel naturality on the Wilson transfer carrier;
--   literal temporal trace/integration naturality;
--   terminal physical transfer spectral gap;
--   cutoff-uniform physical Schur/remainder loss estimates and strict budget.
--
-- Luescher strict positivity is NOT a mass gap.
------------------------------------------------------------------------

import DASHI.Physics.YangMills.BalabanClayHighestAlphaRound60WilsonRPG2Validation

import DASHI.Physics.YangMills.BalabanErikssonDLRUniformityAuditExact
import DASHI.Physics.YangMills.BalabanWilsonTransferIntertwinerExact
import DASHI.Physics.YangMills.BalabanTransferKernelTraceNaturalityExact
import DASHI.Physics.YangMills.BalabanDirectTransferSchurGapWeldExact

import DASHI.Physics.YangMills.BalabanReducedFlatFaddeevPopovKernelExact
import DASHI.Physics.YangMills.BalabanReducedFlatFaddeevPopovGreenInverseExact
import DASHI.Physics.YangMills.BalabanReducedFlatFaddeevPopovIsomorphismExact
import DASHI.Physics.YangMills.BalabanReducedGhostExplicitTraceCarrierExact
import DASHI.Physics.YangMills.BalabanFiniteRationalMatrixTraceCyclicExact
import DASHI.Physics.YangMills.BalabanReducedFaddeevPopovRelativePerturbationExact
import DASHI.Physics.YangMills.BalabanReducedGhostOperatorMatrixExact
import DASHI.Physics.YangMills.BalabanReducedFaddeevPopovTraceLogJetExact
import DASHI.Physics.YangMills.BalabanReducedFaddeevPopovMatrixTraceLogJetExact
import DASHI.Physics.YangMills.BalabanReducedGhostAdjointFourthJetExact
import DASHI.Physics.YangMills.BalabanReducedFaddeevPopovPhysicalFourthJetExact
import DASHI.Physics.YangMills.BalabanReducedGhostNeumannRowContractionExact
import DASHI.Physics.YangMills.BalabanReducedGhostFourthOrderRowContractionExact
import DASHI.Physics.YangMills.BalabanReducedGhostAnchoredRelativeContractionExact
import DASHI.Physics.YangMills.BalabanReducedGhostMatrixLogFifthTailExact
import DASHI.Physics.YangMills.BalabanReducedGhostPhysicalMatrixLogFifthTailExact
import DASHI.Physics.YangMills.BalabanReducedGhostMatrixLogShiftedTailExact
import DASHI.Physics.YangMills.BalabanReducedGhostSignedMatrixLogTailExact
import DASHI.Physics.YangMills.BalabanReducedGhostDyadicCauchyBudgetExact
import DASHI.Physics.YangMills.BalabanReducedGhostTraceFastCauchyCompletionExact

import DASHI.Physics.YangMills.BalabanCMP109BishopSourceRadiusEndpointExact
import DASHI.Physics.YangMills.BalabanCMP109BishopPrincipalLogSourcePackageExact
import DASHI.Physics.YangMills.BalabanCMP109BishopPrincipalLogAdPolynomialExact
import DASHI.Physics.YangMills.BalabanBooleanFourCubeWalshCharacterExact
import DASHI.Physics.YangMills.BalabanCMP109WalshCharacterOrbitCancellationExact
import DASHI.Physics.YangMills.BalabanCMP109WalshFourOrbitFactorizationExact

-- Older sufficient G2 routes remain imported for comparison only.
import DASHI.Physics.YangMills.BalabanChargeRelativeG2AggregateRatioExact
import DASHI.Physics.YangMills.BalabanChargeRelativeG2HeadroomAllocationExact
import DASHI.Physics.YangMills.BalabanSelectedConstraintGramReducedCoercivityExact
import DASHI.Physics.YangMills.BalabanSelectedBackgroundRationalCombesThomasWeightEnvelopeExact
import DASHI.Physics.YangMills.BalabanSelectedKKTWeightedToOrdinaryRowBoundExact
import DASHI.Physics.YangMills.BalabanSelectedWilsonCanonicalG2InputsExact

-- Highest-alpha rank-independent / degree-one G2 route.
import DASHI.Physics.YangMills.BalabanSelectedGaugeReducedLinearClosureExact
import DASHI.Physics.YangMills.BalabanSelectedProjectedSchurGreenPreservesReducedExact
import DASHI.Physics.YangMills.BalabanKKTPseudoinverseConstraintImageEnergyContractionExact
import DASHI.Physics.YangMills.BalabanCanonicalGreenDegreeStatePreimageExact
import DASHI.Physics.YangMills.BalabanCanonicalGreenStateNormReductionExact
import DASHI.Physics.YangMills.BalabanPlaquetteBoundaryCellsPairwiseDistinctExact
import DASHI.Physics.YangMills.BalabanPlaquetteSubsetMobiusDegreeOneCollapseExact
import DASHI.Physics.YangMills.BalabanCanonicalGreenHigherMobiusDegreeVanishExact
import DASHI.Physics.YangMills.BalabanCanonicalGreenDegreeOneOnlyExact
import DASHI.Physics.YangMills.BalabanPlaquetteBoundaryStateNormChargeExact
import DASHI.Physics.YangMills.BalabanChargeRelativeDegreeOneG2ClosureExact

import DASHI.Physics.YangMills.YangMillsCompactSimpleCasimirDynkinTraceExact
import DASHI.Physics.YangMills.BalabanContinuumProkhorovSubsequenceExact
import DASHI.Physics.YangMills.BalabanContinuumScaleLocalObservableCauchyExact
import DASHI.Physics.YangMills.YangMillsContinuumFourthCumulantNonGaussianExact
