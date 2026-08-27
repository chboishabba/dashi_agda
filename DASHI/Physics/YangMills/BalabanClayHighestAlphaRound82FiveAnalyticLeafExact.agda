module DASHI.Physics.YangMills.BalabanClayHighestAlphaRound82FiveAnalyticLeafExact where

------------------------------------------------------------------------
-- ROUND82: SHORTEST HONEST NEW-ANALYSIS CUTSET = FIVE
--
-- Round81 had six independent NEW analytic leaves:
--
--   A1 LiteralCompactSimplePositiveBeta
--   A2 SameFamilySummableContinuumIncrement
--   B1 UniformHeatHessianDebt
--   B2 UniformCovariantFiniteSpeed
--   C1 SameFamilyCompositeOPERemainder
--   C2 SameFamilyStressWardHamiltonian
--
-- ROUND82 ELIMINATION
--
-- A2 is no longer independent on the source-accepting route.
--
-- CMP116/CMP119 already contain the normalized local-expectation mechanism
-- Round81 had isolated as a prospective new theorem:
--
--   * CMP116: the localization/exponentiated-cluster construction is general;
--     Lemma 3 / (2.38) preserves a positive exponential localization rate.
--   * CMP119 (3.44)--(3.47): numerator and denominator of a normalized
--     expectation are expanded together; the surviving terms are anchored on
--     the inserted bond/point and inherit the source exponential bound.
--   * immediately after (3.47): interior localized terms are independent of the
--     finite region and coincide with the whole-lattice terms, giving compatible
--     finite-cutoff partial sums rather than unrelated subsequences.
--   * after (2.42): one unit of exponential localization is explicitly spent to
--     obtain a dyadic factor before summing the scale indices.
--
-- Hence, conditional on the SAME small-effective-coupling history required by
-- the published complete-density theorem, the local normalized response has a
-- summable compatible expansion.  On this shortest dependency graph that small
-- history is supplied by A1.  Ordinary Schwinger insertions and compact-support
-- characteristic phase insertions are two local analytic insertions into the
-- same source-native density, not two new cluster theorems.
--
-- This decrement is therefore
--
--                       6 -> 5
--
-- by removing an independently counted new premise, exactly as Round81 removed
-- the selected-background reproof.  It is NOT a claim that the cited source
-- theorem has been reproved by DASHI.
--
-- A1 SHARPENING -- CURRENT SOURCE-FACING ROUTE
--
-- CMP109 Sect. 5 makes the beta difficulty more precise than the older
-- Wilson/FP/Haar near/far wording suggested.
--
--   * Eq. (5.42) defines beta from the off-diagonal mixed p=0 second derivative
--     of the polarization tensor.
--   * Eq. (5.38) puts the remainder at third and higher lattice-derivative order.
--
-- Therefore global control of the entire polarization tensor is not logically
-- required merely to determine the beta coefficient.  The shortest A1a route is
-- now source-native and determinant-first:
--
--   CMP109 constrained Gaussian operator (1.4)--(1.5)
--     -> exact D^2 log det
--     -> constrained Ward cancellation inside the trace
--     -> U=1 Fourier symbols
--     -> one scalar Brillouin trace/sum
--     -> betaZ_j.
--
-- The old global near/far polarization machinery remains a fallback enclosure
-- after the literal scalar exists; it is not the mandatory first gate.
--
-- At finite coupling the source-native coefficient splits conceptually into the
-- Gaussian leading contribution plus the nonlinear fluctuation contribution
-- from (2.12)--(2.13).  The remaining A1a quantitative work is therefore:
--
--   betaZ_j >= b_Z > 0
--   |betaInt_j| <= C_int g_j^rho
--
-- with rho and uniformity derived from the source rather than inserted from
-- perturbative folklore.
--
-- CMP109 also says after (5.42) that beta_j depends on all preceding effective
-- couplings although the notation beta_j(g_(j-1)) suppresses that dependence.
-- Thus the shortest A1b target is coefficient-relative history response decay,
-- e.g.
--
--   |R_{j,k}| <= C_R theta^(j-k),   theta < 1,
--
-- or any equivalent uniformly summable source-native response estimate.  A
-- contraction theorem for the entire RG state is stronger than required if the
-- beta response itself is summable.
--
-- The Row-A1 physical closure margin is therefore organized by THREE quantities:
--
--   b_Z
--   finite-g interaction debt
--   history-response debt
--
-- and A1 closes once the literal same-trajectory margin is strictly positive.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanTopDownSummableRGIncrementLeafEliminationExact
import DASHI.Physics.YangMills.BalabanCMP119CompatibleLocalExpectationFlowExact
import DASHI.Physics.YangMills.BalabanNormalizedExpectationCrossNumeratorExact
import DASHI.Physics.YangMills.BalabanBetaHistoryLocalizedInfluenceExact
import DASHI.Physics.YangMills.BalabanClayHighestAlphaRound81SixAnalyticLeafExact

round82ActualNewAnalyticLeafCount : Nat
round82ActualNewAnalyticLeafCount = 5

------------------------------------------------------------------------
-- FIVE LIVE NEW-ANALYSIS THEOREMS
------------------------------------------------------------------------

-- A1. Literal compact-simple positive beta on the source trajectory.  The
-- shortest current source-facing decomposition is:
--
--   (i)   positive constrained-Gaussian betaZ from the direct p=0 second jet;
--   (ii)  uniformly small finite-g nonlinear interaction debt;
--   (iii) uniformly summable history-response debt.
--
-- The older global Wilson/FP/Haar near/far scalar route remains a valid fallback
-- numerical enclosure but is not counted as an additional independent leaf.
literalCompactSimplePositiveBetaLevel : ProofLevel
literalCompactSimplePositiveBetaLevel = conditional

-- B1. Same finite-cutoff density: cutoff/volume-uniform integrable heat-Hessian
-- debt, yielding a strictly positive temporal relaxation parameter.
uniformHeatHessianDebtLevel : ProofLevel
uniformHeatHessianDebtLevel = conditional

-- B2. Same heat/Langevin evolution: cutoff/volume-uniform covariant derivative
-- propagation in PHYSICAL distance, hence exponential connected clustering and
-- a positive gap on the reconstructed same-family Hamiltonian.
uniformCovariantFiniteSpeedLevel : ProofLevel
uniformCovariantFiniteSpeedLevel = conditional

-- C1. Same continuum family: renormalized gauge-invariant local composites and
-- quantitative nonperturbative OPE remainder tending to zero at short distance.
sameFamilyCompositeOPERemainderLevel : ProofLevel
sameFamilyCompositeOPERemainderLevel = conditional

-- C2. Same continuum family: local symmetric stress tensor, Ward conservation,
-- and identification of integral T00 with the exact reconstructed Hamiltonian.
sameFamilyStressWardHamiltonianLevel : ProofLevel
sameFamilyStressWardHamiltonianLevel = conditional

------------------------------------------------------------------------
-- SOURCE-OWNED / NON-INDEPENDENT ON THIS ROUTE
------------------------------------------------------------------------

sameFamilySummableContinuumIncrementLevel : ProofLevel
sameFamilySummableContinuumIncrementLevel = standardImported

-- The source theorem still depends on A1's small-coupling history.  Thus A2 has
-- not disappeared physically; it has become a downstream theorem of A1 plus
-- published analysis instead of a second independent new 4D YM lemma.
sameFamilyIncrementDependsOnPositiveBetaLevel : ProofLevel
sameFamilyIncrementDependsOnPositiveBetaLevel = machineChecked

-- Current strict scoreboard: 5 -> 4 only when one of the five conditional NEW
-- theorem roles above is proved, or rigorously eliminated as an independent
-- premise of the shortest source-accepting Clay route.
------------------------------------------------------------------------
