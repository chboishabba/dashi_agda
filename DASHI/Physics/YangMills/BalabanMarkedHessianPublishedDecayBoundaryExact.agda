module DASHI.Physics.YangMills.BalabanMarkedHessianPublishedDecayBoundaryExact where

------------------------------------------------------------------------
-- ROUND73: CMP109 ALREADY OWNS THE DIFFERENTIATED MARKED E^(2) DECAY SHAPE
--
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban,
-- "Propagators for Lattice Gauge Theories in a Background Field",
-- Communications in Mathematical Physics 99(3) (1985), 389--434.
-- DOI: 10.1007/BF01240355.
-- Theorem 3.14 / equation (3.154) supplies the marked domain-sequence
-- propagator comparison: common localized random-walk terms cancel and each
-- survivor gains an extra distance-to-discrepancy exponential factor.
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I.
-- Generation of Effective Actions in a Small Field Approximation and a
-- Coupling Constant Renormalization in Four Dimensions",
-- Communications in Mathematical Physics 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223.
--
-- Source-critical Round73 observation:
-- * Sect. 4 has ALREADY taken the external field derivatives before the active
--   localization step.
-- * (4.3)--(4.5) give the differentiated tree/locality estimates.
-- * the analysis is explicitly reduced to E^(2) in (4.34)--(4.35).
-- * immediately after (4.35), replacing the domain-dependent H_j(Omega_0) by
--   the free-boundary H_j is stated to give an additional factor of the form
--
--       B_0 exp(-delta_0 * marked-distance),
--
--   in the bound of the corresponding E^(2) expression.
-- * (4.36) controls the localization-domain extension and (4.37) defines
--
--       Pi_{mu nu}(x,y) = sum_X E^(2)_{mu nu}(X;x,y).
--
-- * Sect. 5, equation (5.10), records exponential position-space decay of Pi
--   with a strictly positive rate delta_1 inherited from the preceding
--   localization constants.
--
-- Therefore "derive marked decay for the twice-differentiated activity" is
-- NOT an independent new Yang--Mills theorem.  It is source-owned by CMP109,
-- using the CMP99(3) background-propagator machinery.  The live task is only
-- SAME-OBJECT IDENTIFICATION: prove that the E^(2)/Pi activity and source
-- normalization appearing here are literally the derivative/Hessian coordinate
-- of DASHI's unified physical RG state.
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. II.
-- Cluster Expansions", Communications in Mathematical Physics 116(1) (1988),
-- 1--22. DOI: 10.1007/BF01239022.
-- CMP116 supplies the generalized-random-walk localization and residual
-- tree-length summability used by the effective-action construction.
--
-- TREE/FOREST CALIBRATION ONLY
--
-- David C. Brydges and Paul Federbush,
-- "A New Form of the Mayer Expansion in Classical Statistical Mechanics",
-- Journal of Mathematical Physics 19 (1978), 2064--2067.
-- DOI: 10.1063/1.523586.
--
-- David C. Brydges and Thomas Kennedy,
-- "Mayer Expansions and the Hamilton-Jacobi Equation",
-- Journal of Statistical Physics 48 (1987), 19--49.
-- DOI: 10.1007/BF01010398.
--
-- Abdelmalek Abdesselam and Vincent Rivasseau,
-- "Trees, Forests and Jungles: A Botanical Garden for Cluster Expansions",
-- in Constructive Physics, Lecture Notes in Physics 446 (1995), 7--36.
-- DOI: 10.1007/3-540-59190-7_20. arXiv:hep-th/9409094.
--
-- These tree/forest identities calibrate connected-graph/tree resummation.
-- They are NOT the authority for Bałaban's common-domain walk cancellation.
------------------------------------------------------------------------

open import DASHI.Physics.YangMills.CompactLieProofLevel

-- Published/source-owned marked background-propagator domain comparison.
cmp99BackgroundPropagatorMarkedDifferenceLevel : ProofLevel
cmp99BackgroundPropagatorMarkedDifferenceLevel = standardImported

-- Published/source-owned differentiated E^(2) tree/locality structure.
cmp109DifferentiatedActivityTreeStructureLevel : ProofLevel
cmp109DifferentiatedActivityTreeStructureLevel = standardImported

-- Published/source-owned differentiated MARKED domain replacement and
-- resummed exponential polarization-kernel decay, by (4.35)--(4.37), (5.10).
cmp109DifferentiatedMarkedActivityDecayLevel : ProofLevel
cmp109DifferentiatedMarkedActivityDecayLevel = standardImported

-- Published/source-owned generalized-walk cluster localization and residual
-- tree summability.
cmp116GeneralizedRandomWalkClusterLocalisationLevel : ProofLevel
cmp116GeneralizedRandomWalkClusterLocalisationLevel = standardImported

-- Standard connected-graph/tree/forest resummation technology, deliberately
-- separate from the source-native paired common-domain cancellation.
treeForestResummationCalibrationLevel : ProofLevel
treeForestResummationCalibrationLevel = standardImported

-- In-repo finite algebra remains useful for auditing the source mechanism:
-- scalar/noncommutative factor telescopes, common-walk cancellation, and the
-- exponential-shell -> dyadic/weighted-row conversion are theorem-constructed.
finiteDifferentiatedReplacementAndResummationLevel : ProofLevel
finiteDifferentiatedReplacementAndResummationLevel = machineChecked

-- Cauchy extraction is retained as a fallback/check only.  It is not needed to
-- manufacture D^2 E because CMP109 already works at E^(2).
genericCauchyDifferentiationFallbackLevel : ProofLevel
genericCauchyDifferentiationFallbackLevel = machineChecked

------------------------------------------------------------------------
-- TRUE LIVE SEAM AFTER ROUND73
--
-- This is a SAME-OBJECT theorem, not a new decay estimate:
-- identify the source E^(2)/Pi of CMP109 on the literal Bałaban effective
-- density with the twice-field-differentiated activity/Hessian coordinate used
-- by `PhysicalUnifiedOneStepYMEstimate`, preserving scale/background/history
-- normalization.  Once this identification is made, the source exponential
-- decay feeds the existing dyadic and (3/2)-weighted Hessian-row compilers.
--
-- This seam should be discharged inside either
--   LiteralStateEntersPublishedBalabanRG
-- or
--   PhysicalUnifiedOneStepYMEstimate,
-- and is no longer counted as an independent analytic Lemma 7.
------------------------------------------------------------------------

physicalCMP109E2IsUnifiedRGHessianCoordinateLevel : ProofLevel
physicalCMP109E2IsUnifiedRGHessianCoordinateLevel = conditional
