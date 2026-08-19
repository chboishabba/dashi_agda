module DASHI.Physics.YangMills.BalabanClayHighestAlphaRound72MarkedSecondVariationValidation where

------------------------------------------------------------------------
-- ROUND72 FOCUSED ROOT
--
-- Highest-alpha refinement of Lemma 7:
--
--   published CMP99(3) marked propagator/domain decay
--      + CMP109 ALREADY-DIFFERENTIATED E^(2) tree representation
--      + one source-native marked factor replacement bound
--      + finite replacement telescope already owned in-repo
--      + CMP116 generalized-walk/tree resummation
--   ---------------------------------------------------------------
--      marked differentiated-activity exponential localization
--      -> dyadic / (3/2)-weighted Hessian row
--      -> multiscale curvature + quasi-local propagation
--      -> spatial clustering -> OS Hamiltonian gap.
--
-- This supersedes the looser Round71 phrasing "derive the Hessian marked decay
-- by Cauchy".  CMP109 has already taken the two external field variations by
-- the active localization step.  Generic Cauchy machinery remains a fallback,
-- not the primary source-native proof.
--
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban,
-- "Propagators for Lattice Gauge Theories in a Background Field",
-- CMP 99(3) (1985), 389--434. DOI: 10.1007/BF01240355.
-- Theorem 3.14/(3.154): marked domain-sequence difference decay.
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I.
-- Generation of Effective Actions in a Small Field Approximation and a
-- Coupling Constant Renormalization in Four Dimensions",
-- CMP 109 (1987), 249--301. DOI: 10.1007/BF01215223.
-- Equations (4.3)--(4.5), the n=2 specialization (4.35), and resummation
-- (4.37) are the source-native differentiated lane.
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. II.
-- Cluster Expansions", CMP 116(1) (1988), 1--22.
-- DOI: 10.1007/BF01239022.
--
-- TREE/FOREST CROSS-CHECKS
--
-- David C. Brydges and Paul Federbush,
-- "A New Form of the Mayer Expansion in Classical Statistical Mechanics",
-- J. Math. Phys. 19 (1978), 2064--2067. DOI: 10.1063/1.523586.
--
-- David C. Brydges and Thomas Kennedy,
-- "Mayer Expansions and the Hamilton-Jacobi Equation",
-- J. Stat. Phys. 48 (1987), 19--49.
--
-- Abdelmalek Abdesselam and Vincent Rivasseau,
-- "Trees, Forests and Jungles: A Botanical Garden for Cluster Expansions",
-- Lecture Notes in Physics 446 (1995), 7--36.
-- DOI: 10.1007/3-540-59190-7_20. arXiv:hep-th/9409094.
--
-- Guardrail: BBF/Brydges--Kennedy/forest formulae calibrate connected
-- graph/tree resummation only.  They do not justify CMP99 common-domain walk
-- cancellation; that equality comes from the paired restricted background data.
------------------------------------------------------------------------

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanClayHighestAlphaRound70PolchinskiFiniteSpeedValidation
import DASHI.Physics.YangMills.BalabanMarkedHessianPublishedDecayBoundaryExact
import DASHI.Physics.YangMills.BalabanDecoupledActivityHessian
import DASHI.Physics.YangMills.BalabanMarkedPolarisationResummation
import DASHI.Physics.YangMills.BalabanExponentialToDyadicShellCoarseningExact
import DASHI.Physics.YangMills.BalabanSourceExponentialToWeightedHessianExact

round72PublishedMarkedPropagatorDecayLevel : ProofLevel
round72PublishedMarkedPropagatorDecayLevel = standardImported

round72PublishedDifferentiatedActivityTreeStructureLevel : ProofLevel
round72PublishedDifferentiatedActivityTreeStructureLevel = standardImported

round72PublishedGeneralizedWalkClusterLocalisationLevel : ProofLevel
round72PublishedGeneralizedWalkClusterLocalisationLevel = standardImported

-- In-repo theorem-producing algebra already closes the finite factor
-- telescope, finite common-walk cancellation/resummation, exponential->dyadic
-- shell conversion, and direct exponential->weighted-row conversion.
round72FiniteDifferentiatedReplacementTelescopeLevel : ProofLevel
round72FiniteDifferentiatedReplacementTelescopeLevel = machineChecked

round72FiniteMarkedWalkResummationLevel : ProofLevel
round72FiniteMarkedWalkResummationLevel = machineChecked

round72ExponentialShellToWeightedRowLevel : ProofLevel
round72ExponentialShellToWeightedRowLevel = machineChecked

------------------------------------------------------------------------
-- TRUE REMAINING LEMMA 7 PRIMITIVE
--
-- For each replacement term in the literal CMP109 (4.3)--(4.5)
-- differentiated tree expression, insert exactly one marked CMP99(3)
-- propagator/background-domain difference and bound all unchanged factors by
-- their ordinary CMP109 tree estimates.  The result must retain BOTH:
--
--   (i) distance-to-nearest-change decay,
--   (ii) a still-positive residual tree/localization exponent.
--
-- Schematic target after the finite telescope/resummation:
--
-- |E^(2)_Ω(X;x,y) - E^(2)_Ω'(X;x,y)|
--   <= C exp(-δ |x-y|)
--        exp(-κ tree(X))
--        exp(-δ0 D(Ω,Ω';x,y)).
--
-- Once this TERMWISE physical inequality is supplied, the existing modules
-- construct the complete marked Hessian shell and weighted quasi-local row.
-- There is no further independent "Hessian quasi-locality" theorem required.
------------------------------------------------------------------------

round72PhysicalDifferentiatedMarkedReplacementTermBoundLevel : ProofLevel
round72PhysicalDifferentiatedMarkedReplacementTermBoundLevel = conditional

-- Downstream same-object identifications still required for the full mass-gap
-- role: Polchinski covariance/curvature on the same effective density and the
-- compact-group Langevin derivative generator controlled by this Hessian.
round72PhysicalSameDensityPolchinskiCurvatureLevel : ProofLevel
round72PhysicalSameDensityPolchinskiCurvatureLevel = conditional

round72PhysicalCompactGroupDerivativePropagationLevel : ProofLevel
round72PhysicalCompactGroupDerivativePropagationLevel = conditional
