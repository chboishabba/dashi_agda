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
-- * the ACTUAL alternating signed degree-five tail is constructed with the
--   same 1/2500 row cap, so alternating signs cost no extra norm;
-- * shifted tails have modulus
--       rowMass(Tail_m) <= (1/5)^m / 2500 <= (1/2)^m;
-- * the safe redundant trace cost 768 is absorbed by the fifth-tail factor.
-- Remaining ghost closure is finite same-object prefix/tail splitting followed
-- by standard finite principal-log/determinant functional calculus. These are
-- supporting finite-analysis lemmas, not independent YM research producers.
--
-- CMP109 / ONE-LOOP ROUTE
-- * source-radius inverse-dexp coefficient is actual Bishop-real data;
-- * 0 <= beta(1/12)-1/12 <= 1/14400 and symmetric coefficient >=23/24;
-- * J=I+c1 ad_X+beta ad_X^2 is literal Bishop-real operator data;
-- * source Euclidean reflection covariance kills every nontrivial (C2)^4
--   Walsh sector exactly BEFORE interval arithmetic;
-- * permutation covariance then reduces the 240 regular Brillouin cells to
--   four trivial-character representatives with weights 64,96,64,16;
-- * weighted monotonicity now proves four representative Bishop lower bounds
--   imply the lower bound for the complete 240-cell regular contribution.
-- Remaining one-loop producer is the same-object Wilson/FP/Haar scalar
-- identification, four representative Bishop enclosures, the finite literal
-- interaction O(g^4) atom bounds, and the positive colour/orbit endpoint.
--
-- G2 / KKT ROUTE -- EXACT DEGREE COLLAPSE + POLARIZATION FALSIFIER
-- * projected Schur Green preserves the mean-zero computational quotient, but
--   is not silently identified with raw background-dependent Moore--Penrose K+;
-- * stabilizer stratification rejects a background-uniform raw rowMass(K+) as
--   a necessary G2 dependency;
-- * canonical subset states are literal constraint images
--       s_S=L(P_S g), delta_S=L(P_S w);
-- * the KKT repair is an orthogonal projector, giving rank-independently
--       <L v,K+ L v> = ||L* K+ L v||^2 <= ||v||^2;
-- * the four plaquette boundary cells are pairwise distinct;
-- * subset localization is therefore additive:
--       L1=P_p v, L2=3 L1, L3=3 L1, L4=L1;
-- * exact Rota/Mobius formulas force source/defect D2=D3=D4=0;
-- * hence FIFTEEN of sixteen canonical Green degree blocks vanish exactly;
-- * the literal defect D1 state satisfies
--       3 ||w_1||^2 = C_p(h),
--   so its separate norm ratio is exactly 1/3;
-- * this exact value FALSIFIES the tempting state-norm/polarization compiler:
--       (1/2)(1/3)=1/6
--   already exceeds the entire singleton target 55/18874368 by >57195x,
--   before any raw/source majorant is spent;
-- * therefore the live route retains signed cancellation before majorisation:
--       R_corr = (R1-G11) + (R2+R3+R4).
-- * the highest-alpha compiler now needs exactly TWO physical estimates:
--       R1-G11       <= a Q,
--       R2+R3+R4     <= b Q,
--   and closes whenever a+b <= 55/18874368.
-- No K+ row bound, LBB constant, source/defect norm majorisation, or sixteen
-- Green-cell interval family remains on the live G2 critical path.
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
-- physical exponential clustering. Clustering -> Hamiltonian gap is downstream
-- standard OS/spectral closure, not another YM estimate.
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
import DASHI.Physics.YangMills.BalabanCMP109WalshFiniteModeFourRepresentativeLowerExact

-- Older G2 routes retained as comparison/falsifier history only.
import DASHI.Physics.YangMills.BalabanChargeRelativeG2AggregateRatioExact
import DASHI.Physics.YangMills.BalabanChargeRelativeG2HeadroomAllocationExact
import DASHI.Physics.YangMills.BalabanSelectedConstraintGramReducedCoercivityExact
import DASHI.Physics.YangMills.BalabanSelectedBackgroundRationalCombesThomasWeightEnvelopeExact
import DASHI.Physics.YangMills.BalabanSelectedKKTWeightedToOrdinaryRowBoundExact
import DASHI.Physics.YangMills.BalabanSelectedWilsonCanonicalG2InputsExact
import DASHI.Physics.YangMills.BalabanChargeRelativeCanonicalStateNormG2ClosureExact
import DASHI.Physics.YangMills.BalabanChargeRelativeDegreeOneG2ClosureExact
import DASHI.Physics.YangMills.BalabanChargeRelativeDegreeOneG2ExactDefectCompiler

-- Exact rank-independent geometry and current live correlated-D1 G2 route.
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
import DASHI.Physics.YangMills.BalabanDegreeOneStateNormG2HeadroomNoGoExact
import DASHI.Physics.YangMills.BalabanCanonicalCorrelatedDegreeOneBeforePolarizationExact
import DASHI.Physics.YangMills.BalabanChargeRelativeCorrelatedD1G2ClosureExact

import DASHI.Physics.YangMills.YangMillsCompactSimpleCasimirDynkinTraceExact
import DASHI.Physics.YangMills.BalabanContinuumProkhorovSubsequenceExact
import DASHI.Physics.YangMills.BalabanContinuumScaleLocalObservableCauchyExact
import DASHI.Physics.YangMills.YangMillsContinuumFourthCumulantNonGaussianExact
