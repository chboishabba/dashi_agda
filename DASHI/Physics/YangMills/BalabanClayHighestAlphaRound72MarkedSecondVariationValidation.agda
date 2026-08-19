module DASHI.Physics.YangMills.BalabanClayHighestAlphaRound72MarkedSecondVariationValidation where

------------------------------------------------------------------------
-- ROUND73 FOCUSED ROOT (file name retained for stacked import stability)
--
-- Highest-alpha correction to the Round72 8-lemma cutset:
--
-- CMP109 itself already performs the relevant TWO field variations before the
-- marked localization step.  After (4.35) it states that replacing the
-- domain-dependent H_j(Omega_0) by its free-boundary version supplies an extra
-- exponential marked-distance factor in the bound of the corresponding E^(2)
-- expression; (4.36)--(4.37) extend/resum the localization-domain family, and
-- Sect. 5 equation (5.10) records exponential position-space decay of Pi.
--
-- Therefore the old independent item
--
--     MarkedDifferentiatedActivityExponentialLocalisation
--
-- is SOURCE-OWNED rather than new Yang--Mills analysis.  Its only live seam is
-- same-object identification of CMP109's E^(2)/Pi with the Hessian/derivative
-- coordinate of the literal unified RG state.  That identification belongs in
-- `LiteralStateEntersPublishedBalabanRG` / `PhysicalUnifiedOneStepYMEstimate`.
--
-- The mass-gap lane is now:
--
--   source-owned CMP99(3)+CMP109 differentiated marked decay
--      -> SAME unified-RG Hessian coordinate
--      -> existing exponential/dyadic/(3/2)-weighted row compilers
--      -> same-density Polchinski curvature
--      -> compact-Lie Langevin commutator
--         = symmetric Hessian + onsite ad-skew connection
--      -> exact sitewise skew quadratic cancellation
--      -> weighted propagation + temporal relaxation
--      -> spatial clustering -> SAME-family OS Hamiltonian gap.
--
-- This is a genuine 8 -> 7 analytic-cutset reduction, not a relabelling.
------------------------------------------------------------------------

-- PRIMARY SOURCES
--
-- Tadeusz Bałaban,
-- "Propagators for Lattice Gauge Theories in a Background Field",
-- CMP 99(3) (1985), 389--434. DOI: 10.1007/BF01240355.
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I.
-- Generation of Effective Actions in a Small Field Approximation and a
-- Coupling Constant Renormalization in Four Dimensions",
-- CMP 109 (1987), 249--301. DOI: 10.1007/BF01215223.
-- Source anchors: (4.3)--(4.5), (4.35)--(4.37), (5.10).
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. II.
-- Cluster Expansions", CMP 116(1) (1988), 1--22.
-- DOI: 10.1007/BF01239022.
--
-- Brian C. Hall,
-- "Lie Groups, Lie Algebras, and Representations: An Elementary Introduction",
-- second edition, GTM 222, Springer (2015).
-- DOI: 10.1007/978-3-319-13467-3.
--
-- John Milnor,
-- "Curvatures of Left Invariant Metrics on Lie Groups",
-- Advances in Mathematics 21 (1976), 293--329.
-- DOI: 10.1016/S0001-8708(76)80002-3.
--
-- TREE/FOREST CROSS-CHECKS ONLY
-- David C. Brydges and Paul Federbush,
-- "A New Form of the Mayer Expansion in Classical Statistical Mechanics",
-- J. Math. Phys. 19 (1978), 2064--2067. DOI: 10.1063/1.523586.
-- David C. Brydges and Thomas Kennedy,
-- "Mayer Expansions and the Hamilton-Jacobi Equation",
-- J. Stat. Phys. 48 (1987), 19--49. DOI: 10.1007/BF01010398.
-- Abdelmalek Abdesselam and Vincent Rivasseau,
-- "Trees, Forests and Jungles: A Botanical Garden for Cluster Expansions",
-- LNP 446 (1995), 7--36. DOI: 10.1007/3-540-59190-7_20.
--
-- Guardrail: tree/forest formulas calibrate resummation; Bałaban's exact
-- common-domain cancellation comes from equality of paired restricted
-- background data, not from BBF itself.
------------------------------------------------------------------------

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanClayHighestAlphaRound70PolchinskiFiniteSpeedValidation
import DASHI.Physics.YangMills.BalabanMarkedHessianPublishedDecayBoundaryExact
import DASHI.Physics.YangMills.BalabanDecoupledActivityHessian
import DASHI.Physics.YangMills.BalabanDifferentiatedMarkedFactorProductExact
import DASHI.Physics.YangMills.BalabanNoncommutativeMarkedOperatorProductExact
import DASHI.Physics.YangMills.BalabanMarkedPolarisationResummation
import DASHI.Physics.YangMills.BalabanExponentialToDyadicShellCoarseningExact
import DASHI.Physics.YangMills.BalabanSourceExponentialToWeightedHessianExact
import DASHI.Physics.YangMills.CompactLieBiInvariantSkewLangevinExact
import DASHI.Physics.YangMills.CompactLieLangevinSkewConnectionCancellationExact

------------------------------------------------------------------------
-- SOURCE-OWNED DIFFERENTIATED MARKED LOCALISATION
------------------------------------------------------------------------

round73PublishedMarkedPropagatorDecayLevel : ProofLevel
round73PublishedMarkedPropagatorDecayLevel = standardImported

round73PublishedDifferentiatedActivityTreeStructureLevel : ProofLevel
round73PublishedDifferentiatedActivityTreeStructureLevel = standardImported

round73PublishedDifferentiatedMarkedE2DecayLevel : ProofLevel
round73PublishedDifferentiatedMarkedE2DecayLevel = standardImported

round73PublishedGeneralizedWalkClusterLocalisationLevel : ProofLevel
round73PublishedGeneralizedWalkClusterLocalisationLevel = standardImported

------------------------------------------------------------------------
-- OWNED FINITE / QUASI-LOCAL ASSEMBLY
------------------------------------------------------------------------

round73NoncommutativeMarkedOperatorAssemblyLevel : ProofLevel
round73NoncommutativeMarkedOperatorAssemblyLevel = machineChecked

round73ScalarMarkedProductAssemblyLevel : ProofLevel
round73ScalarMarkedProductAssemblyLevel = machineChecked

round73FiniteMarkedWalkResummationLevel : ProofLevel
round73FiniteMarkedWalkResummationLevel = machineChecked

round73ExponentialShellToWeightedRowLevel : ProofLevel
round73ExponentialShellToWeightedRowLevel = machineChecked

round73BasisFreeAdSkewCancellationLevel : ProofLevel
round73BasisFreeAdSkewCancellationLevel = machineChecked

------------------------------------------------------------------------
-- LIVE SAME-OBJECT SEAMS
--
-- S0 belongs inside the unified physical RG theorem, not as an independent
-- decay lemma: identify source E^(2)/Pi with the derivative/Hessian coordinate
-- of the SAME literal effective density and norm.
--
-- S1 identifies that same density/covariance path with the exact Polchinski
-- C_t, dot C_t, ddot C_t and proves the multiscale curvature/debt inequality.
--
-- S2 proves the literal compact-group lattice Langevin commutator.  The
-- connection part then contributes exactly zero quadratic derivative energy by
-- the basis-free Ad-invariant theorem; no second positive growth budget exists.
--
-- S3 is the standard weighted-Gronwall/temporal-relaxation assembly and
-- same-family passage to Euclidean spatial clustering.
------------------------------------------------------------------------

round73PhysicalCMP109E2IsUnifiedRGHessianCoordinateLevel : ProofLevel
round73PhysicalCMP109E2IsUnifiedRGHessianCoordinateLevel = conditional

round73PhysicalSameDensityPolchinskiCurvatureLevel : ProofLevel
round73PhysicalSameDensityPolchinskiCurvatureLevel = conditional

round73PhysicalLiteralCompactLieLangevinCommutatorLevel : ProofLevel
round73PhysicalLiteralCompactLieLangevinCommutatorLevel = conditional

round73PhysicalWeightedPropagationSameFamilyLevel : ProofLevel
round73PhysicalWeightedPropagationSameFamilyLevel = conditional
