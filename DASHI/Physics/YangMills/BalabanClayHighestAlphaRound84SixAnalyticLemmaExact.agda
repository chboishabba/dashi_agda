module DASHI.Physics.YangMills.BalabanClayHighestAlphaRound84SixAnalyticLemmaExact where

------------------------------------------------------------------------
-- ROUND84: SHORTEST CURRENT HARD-ANALYSIS CUTSET = SIX
--
-- The attached Clay-facing analysis began with five independent packages and an
-- upper count of nine concrete hard analytic lemmas.  Round83 reduced 9 -> 7 by
-- removing downstream finite-speed/clustering and geometric OPE-tail work.
-- Round84 reduces 7 -> 6 by eliminating a second count on the stress lane:
-- once the renormalized stress charge is proved to generate the SAME strongly
-- continuous OS translation group on a common dense core, equality with H_OS is
-- Stone-generator uniqueness, not another four-dimensional Yang--Mills lemma.
--
-- This file also records two trust-boundary corrections discovered while doing
-- the actual source archaeology:
--
-- (i) beta_j's marginal coupling history must NOT be assumed exponentially
--     forgotten.  CMP109 explicitly says dependence on g_{j-1} is important.
--     The beta marked shell controls only localized IRRELEVANT/polymer memory at
--     fixed declared marginal data.  The current-step nonlinear remainder has a
--     separate budget.
--
-- (ii) beta-memory depth, physical spatial separation, and OPE truncation depth
--      are distinct typed marks.  One differentiated analytic theorem may be
--      uniform over the mark kind, but no equality of those metrics is used.
--
-- CURRENT STRICT COUNT
--
--   5 independent Clay theorem packages
--   6 genuinely new physical analytic lemma families
--
-- A future decrement is legitimate only if one of the six conditional roles
-- below is proved, or rigorously becomes standard/source-downstream.  Renaming a
-- field, importing a deferred theorem, or conflating physical grades does not
-- change the count.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanClayHighestAlphaRound83SevenAnalyticLemmaExact
import DASHI.Physics.YangMills.BalabanBetaHistoryLocalizedInfluenceExact
import DASHI.Physics.YangMills.BalabanSharedMarkedAnalyticShellExact
import DASHI.Physics.YangMills.BalabanCompactSimplePositiveBetaFromSharedMarkedShellExact
import DASHI.Physics.YangMills.CompactSimpleClassificationAdjointCasimirExact
import DASHI.Physics.YangMills.BalabanCMP109CompactSimpleColourReductionSourceExact
import DASHI.Physics.YangMills.BalabanCompactSimpleHaarQuadraticCasimirExact
import DASHI.Physics.YangMills.BalabanReducedGhostPrincipalLogDetSourceExact
import DASHI.Physics.YangMills.BalabanFiniteTraceSeriesPrefixTailExact
import DASHI.Physics.YangMills.BalabanPolchinskiShellIntegralDebtExact
import DASHI.Physics.YangMills.YangMillsSharedMarkedCompositeOPERemainderExact
import DASHI.Physics.YangMills.YangMillsLatticeStressWardSliceConservationExact
import DASHI.Physics.YangMills.YangMillsStressWardStoneGeneratorBridgeExact

round84IndependentPackageCount : Nat
round84IndependentPackageCount = 5

round84HardAnalyticLemmaUpperCount : Nat
round84HardAnalyticLemmaUpperCount = 6

------------------------------------------------------------------------
-- SIX LIVE NEW PHYSICAL ANALYTIC LEMMA FAMILIES
------------------------------------------------------------------------

-- L1 / A1: literal same-step compact-simple one-loop theorem.
--
-- On the SAME Bałaban finite-cutoff background carrier:
--   * evaluate the universal constrained Wilson + reduced FP + Haar polarization
--     scalar and normalize it to the source Ward-reduced/classified compact-
--     simple colour factor C_A, obtaining C_A * 11/24;
--   * prove the remaining same-step/Bishop nonlinear remainder has a
--     cutoff/volume/scale/group-uniform radius R_local small enough for the
--     retained positive margin.
--
-- Already downstream/source-owned: CMP109 Ward reduction of the colour tensor
-- to one invariant scalar; uniqueness of the compact-simple invariant bilinear
-- form; strict C_A>0 for all classified simple Lie types; Haar quadratic
-- coefficient C_A/24 in exponential coordinates; the literal reduced ghost
-- fourth jet, row contraction, signed log-tail Cauchy modulus, finite prefix /
-- tail algebra and finite principal-log/log-det functional calculus.
literalCompactSimpleOneLoopAndLocalRemainderLevel : ProofLevel
literalCompactSimpleOneLoopAndLocalRemainderLevel = conditional

-- L2 / A2 + hard source mark consumed by B2a/C1-tail.
--
-- Prove one MARK-PARAMETRIC differentiated source-locality theorem and its
-- literal same-object projections, with distinct grades:
--   beta mark      = localized irrelevant/polymer RG memory at fixed marginal data;
--   Hessian mark   = physical-spatial influence separation;
--   composite mark = RG/OPE truncation/source insertion separation.
--
-- The beta mark does NOT include the marginal g_{j-1} dependence.  Existing
-- exact compilers turn the three marked estimates into a uniform irrelevant-
-- memory beta budget, a weighted spatial Hessian row, and a vanishing composite
-- tail.  Source exponential->dyadic shell-width selection is standard analysis.
physicalMarkedAnalyticSourceAndProjectionLevel : ProofLevel
physicalMarkedAnalyticSourceAndProjectionLevel = conditional

-- L3 / B1: physical heat/Doob Hessian debt.
--
-- On the SAME finite-cutoff density and compact-group heat/Doob interpolation,
-- identify the negative Hessian contribution on each continuous time shell and
-- prove its integral I_n is bounded by the marked/discrete shell debt eta_n.
-- The geometric sum eta_n <= C(17/32)^n -> sum I_n <= (32/15)C is downstream.
-- With the positive compact-simple Ricci reserve, standard inhomogeneous
-- Gamma-calculus then gives a strictly positive uniform LSI/Poincare rate.
physicalPerShellHeatHessianDebtLevel : ProofLevel
physicalPerShellHeatHessianDebtLevel = conditional

-- L4 / C1a: same-family local composite fields.
--
-- Construct the renormalized gauge-invariant curvature/composite local fields as
-- distributions/operators on the SAME continuum Schwinger/OS family produced by
-- the source-native RG limit.  Existing completed-state projection theorems show
-- same-family inheritance once the completed physical carrier exists, but do not
-- themselves construct that carrier or its nuclear test-function continuity.
sameFamilyRenormalizedCurvatureCompositeExistenceLevel : ProofLevel
sameFamilyRenormalizedCurvatureCompositeExistenceLevel = conditional

-- L5 / C1b after tail elimination.
--
-- Identify the physical product-expansion remainder with the composite mark and
-- identify the coefficient functions with the asymptotically-free Yang--Mills
-- short-distance coefficients.  The pure geometric R_D -> 0 modulus is already
-- downstream through `DyadicOPERemainderMajorant`; it is not counted again.
sameFamilyOPEAndAsymptoticFreedomMatchingLevel : ProofLevel
sameFamilyOPEAndAsymptoticFreedomMatchingLevel = conditional

-- L6 / C2 (old C2a+C2b fused at the mathematically correct strength).
--
-- Construct/renormalize symmetric local T_{mu nu} on the SAME continuum, prove
-- the translation Ward identity, control spatial smearing/cutoff removal and
-- domains, and prove the limiting T_{0 nu} charge generates the SAME OS
-- translation group on a common invariant dense core.  Periodic finite-lattice
-- charge conservation is exact in-repo.  Once same-group generation is proved,
-- equality of the stress energy charge with H_OS is Stone uniqueness and is not
-- an independent YM lemma.
sameFamilyStressWardGeneratesOSTranslationsLevel : ProofLevel
sameFamilyStressWardGeneratesOSTranslationsLevel = conditional

------------------------------------------------------------------------
-- DOWNSTREAM / SOURCE-OWNED RESULTS REMOVED FROM THE NEW-ANALYSIS COUNT
------------------------------------------------------------------------

cmp109WardColourScalarReductionLevel : ProofLevel
cmp109WardColourScalarReductionLevel = standardImported

compactSimpleInvariantColourReductionLevel : ProofLevel
compactSimpleInvariantColourReductionLevel = standardImported

classifiedCompactSimpleCasimirAndPositivityLevel : ProofLevel
classifiedCompactSimpleCasimirAndPositivityLevel = machineChecked

compactSimpleHaarQuadraticCasimirLevel : ProofLevel
compactSimpleHaarQuadraticCasimirLevel = machineChecked

reducedGhostFinitePrincipalLogDetLevel : ProofLevel
reducedGhostFinitePrincipalLogDetLevel = standardImported

reducedGhostFinitePrefixTailAlgebraLevel : ProofLevel
reducedGhostFinitePrefixTailAlgebraLevel = machineChecked

compactSimpleTwoChannelPositiveBetaAssemblyLevel : ProofLevel
compactSimpleTwoChannelPositiveBetaAssemblyLevel = machineChecked

-- Deliberate NON-GOAL (not represented by a ProofLevel field): there is no
-- theorem asserting exponential forgetting of the marginal running coupling.
-- CMP109 says the g_{j-1} dependence is important.  Only the irrelevant-memory
-- coordinate is localized/contractive on this route.

sourceExponentialToDyadicWidthLevel : ProofLevel
sourceExponentialToDyadicWidthLevel = standardImported

markedTailAndWeightedRowCompilerLevel : ProofLevel
markedTailAndWeightedRowCompilerLevel = machineChecked

polchinskiShellDebtGeometricSummationLevel : ProofLevel
polchinskiShellDebtGeometricSummationLevel = machineChecked

compactGroupRicciReserveDebtToLSILevel : ProofLevel
compactGroupRicciReserveDebtToLSILevel = standardImported

compositeDyadicOPERemainderModulusLevel : ProofLevel
compositeDyadicOPERemainderModulusLevel = machineChecked

periodicStressWardSliceConservationLevel : ProofLevel
periodicStressWardSliceConservationLevel = machineChecked

stoneSameTranslationGroupGeneratorUniquenessLevel : ProofLevel
stoneSameTranslationGroupGeneratorUniquenessLevel = standardImported

-- No inhabitant of the literal Clay solution contract is asserted here.
------------------------------------------------------------------------
