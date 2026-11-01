module DASHI.Physics.YangMills.BalabanClayHighestAlphaRound81SixAnalyticLeafExact where

------------------------------------------------------------------------
-- ROUND81: SHORTEST HONEST NEW-ANALYSIS CUTSET = SIX
--
-- Round80 counted seven:
--
--   L1 SelectedBackgroundUniformStability
--   L2 LiteralCompactSimplePositiveBeta
--   L3 UnifiedPhysicalRGStep
--   L4 UniformHeatHessianDebt
--   L5 UniformCovariantFiniteSpeed
--   L6 SameFamilyCompositeOPERemainder
--   L7 SameFamilyStressWardHamiltonian
--
-- Two top-down corrections are made here.
--
-- (I) L1 IS SOURCE-OWNED ON THE SHORTEST ROUTE.
--
-- CMP122 Theorem 1 concludes preservation of the complete CMP119 Section-2
-- density class and all of its bounds under the small-effective-coupling
-- hypothesis.  The background/minimizer/propagator estimates are internal to
-- that published proof, not an additional theorem premise.  Round76 already
-- proves the strong state is the SAME published density and transports those
-- Section-2 bounds.  Therefore independently rebuilding selected rational G2
-- stability is no longer a NEW Clay analytic leaf on the source-accepting route.
-- It remains valuable as an independent verification/reconstruction programme.
--
-- (II) OLD L3 WAS STRONGER THAN ITS CONSUMER.
--
-- The continuum construction consumes one literal trajectory with summable
-- successive-scale increments; it does not consume a Banach contraction theorem
-- for arbitrary pairs of RG states.  CMP116/CMP119 themselves are stated in the
-- former, scale-generated-local-activity language.  Thus the shortest L3 is now
-- `SameFamilySummableContinuumIncrement`: prove that the normalized local and
-- characteristic-functional coordinates inherit a summable modulus from the
-- published E/R/B localization bounds.
--
-- SOURCE FACTS USED IN THIS RECUT
--
-- Tadeusz Bałaban,
-- "Convergent Renormalization Expansions for Lattice Gauge Theories",
-- CMP 119 (1988), 243--285. DOI: 10.1007/BF01217741.
--   * (2.31): strong exponential R-term localization;
--   * (2.42): exponential B-term localization;
--   * discussion after (2.42): one exponential unit is converted into an
--     explicit dyadic inter-scale factor before summing over j;
--   * Theorem 1: the complete inductive density class is preserved.
--
-- Tadeusz Bałaban,
-- "Large Field Renormalization. II. Localization, Exponentiation, and Bounds
-- for the R Operation", CMP 122 (1989), 355--392.
-- DOI: 10.1007/BF01238433.
--   * Theorem 1 completes the four-dimensional pure-gauge UV-stability theorem
--     conditional on small effective coupling.
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. II.
-- Cluster Expansions", CMP 116 (1988), 1--22.
-- DOI: 10.1007/BF01239022.
--   * Lemma 3 / (2.38) and (2.41): exponential localization survives the
--     localization/cluster resummation.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanTopDownSelectedBackgroundLeafEliminationExact
import DASHI.Physics.YangMills.BalabanTopDownSummableRGIncrementExact
import DASHI.Physics.YangMills.BalabanFiveShellLargeBranchContractionExact
import DASHI.Physics.YangMills.BalabanClayHighestAlphaRound80SevenAnalyticLeafAttackExact

round81ActualNewAnalyticLeafCount : Nat
round81ActualNewAnalyticLeafCount = 6

------------------------------------------------------------------------
-- SIX LIVE NEW-ANALYSIS THEOREMS
------------------------------------------------------------------------

-- A1. Actual Wilson + reduced FP + Haar history-dependent beta, uniformly
-- positive for arbitrary compact simple G with the exact C_A normalization.
literalCompactSimplePositiveBetaLevel : ProofLevel
literalCompactSimplePositiveBetaLevel = conditional

-- A2. Same normalized source-native finite-cutoff trajectory: published E/R/B
-- tails imply one summable ordinary + characteristic-functional increment
-- modulus.  Existing Cauchy/Minlos/OS compilers then construct the same family.
sameFamilySummableContinuumIncrementLevel : ProofLevel
sameFamilySummableContinuumIncrementLevel = conditional

-- B1. Same finite-cutoff YM density has a uniform integrable heat-Hessian debt.
uniformHeatHessianDebtLevel : ProofLevel
uniformHeatHessianDebtLevel = conditional

-- B2. Same heat/Langevin evolution has uniform covariant quasi-local derivative
-- propagation in physical distance.
uniformCovariantFiniteSpeedLevel : ProofLevel
uniformCovariantFiniteSpeedLevel = conditional

-- C1. Same continuum family has quantitative nonperturbative gauge-invariant
-- composite OPE remainder tending to zero.
sameFamilyCompositeOPERemainderLevel : ProofLevel
sameFamilyCompositeOPERemainderLevel = conditional

-- C2. Same continuum family has the local symmetric stress tensor, Ward
-- conservation and identification of its T00 generator with the reconstructed H.
sameFamilyStressWardHamiltonianLevel : ProofLevel
sameFamilyStressWardHamiltonianLevel = conditional

------------------------------------------------------------------------
-- NOT LIVE LEAVES ON THIS SHORTEST ROUTE
------------------------------------------------------------------------

selectedBackgroundIndependentReproofLevel : ProofLevel
selectedBackgroundIndependentReproofLevel = standardImported

-- Useful stronger statement, but no longer a shortest-route prerequisite.
globalBanachRGMapContractionLevel : ProofLevel
globalBanachRGMapContractionLevel = conditional

-- Current exact frontier: 6 -> 5 occurs only when one of the six conditional
-- physical theorem roles above is actually inhabited.  No package renaming or
-- arithmetic budget optimization changes this count.
------------------------------------------------------------------------
