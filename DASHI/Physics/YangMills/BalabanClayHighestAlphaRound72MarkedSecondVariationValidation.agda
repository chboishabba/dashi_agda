module DASHI.Physics.YangMills.BalabanClayHighestAlphaRound72MarkedSecondVariationValidation where

------------------------------------------------------------------------
-- ROUND73 FOCUSED ROOT (file name retained for stacked import stability)
--
-- Highest-alpha correction INSIDE the Round72 eight-lemma cutset:
--
-- CMP109 itself already performs the relevant TWO field variations before the
-- marked localization step.  After (4.35) it states that replacing the
-- domain-dependent H_j(Omega_0) by its free-boundary version supplies an extra
-- exponential marked-distance factor in the bound of the corresponding E^(2)
-- expression; (4.36)--(4.37) extend/resum the localization-domain family, and
-- Sect. 5 equation (5.10) records exponential position-space decay of Pi.
--
-- Round72 had ALREADY folded differentiated localisation into
-- `PhysicalUnifiedOneStepYMEstimate`.  Therefore this source discovery does
-- not change the authoritative theorem-sized count from eight to seven.  It
-- materially SHRINKS that unified-RG theorem: the decay estimate is
-- source-owned, and its live seam is only same-object identification of
-- CMP109's E^(2)/Pi with the Hessian/derivative coordinate of the literal
-- unified RG state.
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
-- The authoritative eight-item analytic cutset is recorded in
-- `BalabanClayHighestAlphaRound73EightAnalyticCutsetExact`.
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

round73PublishedMarkedPropagatorDecayLevel : ProofLevel
round73PublishedMarkedPropagatorDecayLevel = standardImported

round73PublishedDifferentiatedActivityTreeStructureLevel : ProofLevel
round73PublishedDifferentiatedActivityTreeStructureLevel = standardImported

round73PublishedDifferentiatedMarkedE2DecayLevel : ProofLevel
round73PublishedDifferentiatedMarkedE2DecayLevel = standardImported

round73PublishedGeneralizedWalkClusterLocalisationLevel : ProofLevel
round73PublishedGeneralizedWalkClusterLocalisationLevel = standardImported

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

-- S0 belongs inside the unified physical RG theorem: identify source E^(2)/Pi
-- with the derivative/Hessian coordinate of the SAME literal effective density.
round73PhysicalCMP109E2IsUnifiedRGHessianCoordinateLevel : ProofLevel
round73PhysicalCMP109E2IsUnifiedRGHessianCoordinateLevel = conditional

-- Same-density Polchinski curvature/debt instantiation.
round73PhysicalSameDensityPolchinskiCurvatureLevel : ProofLevel
round73PhysicalSameDensityPolchinskiCurvatureLevel = conditional

-- Literal compact-group Langevin commutator.  Once identified, its connection
-- part is already energy-zero by the basis-free Ad-invariant theorem.
round73PhysicalLiteralCompactLieLangevinCommutatorLevel : ProofLevel
round73PhysicalLiteralCompactLieLangevinCommutatorLevel = conditional

-- Standard weighted propagation + temporal relaxation and passage to the same
-- Euclidean continuum family.
round73PhysicalWeightedPropagationSameFamilyLevel : ProofLevel
round73PhysicalWeightedPropagationSameFamilyLevel = conditional
