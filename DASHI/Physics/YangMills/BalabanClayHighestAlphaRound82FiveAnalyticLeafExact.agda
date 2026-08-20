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
-- A1 SHARPENING
--
-- CMP109 also makes the remaining beta difficulty more precise.  At the end of
-- Sect. 5 Bałaban says beta_j depends on all preceding effective couplings, even
-- though the coefficient is extracted locally from the polarization tensor.
-- `BalabanBetaHistoryLocalizedInfluenceExact` therefore replaces a dangerous
-- history-length times local-error estimate by a summable shell influence:
--
--   influence_d <= C gamma (1/4) 2^-d
--     ==> total history defect <= C gamma / 2.
--
-- Thus A1 no longer needs a bound growing with the number of RG steps.  It needs
-- the literal constrained Gaussian coefficient plus one cutoff-uniform localized
-- history-influence estimate for the same Wilson/FP/Haar polarization scalar.
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

-- A1. Literal Wilson + reduced Faddeev--Popov + Haar coefficient on arbitrary
-- compact simple G.  The universal/zero-history Gaussian coefficient is already
-- separated; the new compiler makes the arbitrary preceding history harmless
-- once its shell influence is summable uniformly.
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
