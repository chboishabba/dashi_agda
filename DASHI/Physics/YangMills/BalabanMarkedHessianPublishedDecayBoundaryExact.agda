module DASHI.Physics.YangMills.BalabanMarkedHessianPublishedDecayBoundaryExact where

------------------------------------------------------------------------
-- ROUND72: PUBLISHED MARKED PROPAGATOR DECAY != DIFFERENTIATED HESSIAN CLOSURE
--
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban,
-- "Propagators for Lattice Gauge Theories in a Background Field",
-- Communications in Mathematical Physics 99(3) (1985), 389--434.
-- DOI: 10.1007/BF01240355.
--
-- The source proves regularity/exponential decay of the background-field
-- propagators and, for differences of propagators on two domains, an extra
-- exponential factor controlled by the distance from the localization to the
-- nearest place where the domains/background data differ.  This is the
-- published zeroth-order marked-domain decay used by the current GAP-1 route.
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I.
-- Generation of Effective Actions in a Small Field Approximation and a
-- Coupling Constant Renormalization in Four Dimensions",
-- Communications in Mathematical Physics 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223.
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. II.
-- Cluster Expansions", Communications in Mathematical Physics 116(1) (1988),
-- 1--22. DOI: 10.1007/BF01239022.
-- CMP116 explicitly constructs the fluctuation-field cluster expansion using
-- generalized random-walk expansions for propagators/minimizers inherited
-- from the background-propagator programme.
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
--
-- Abdelmalek Abdesselam and Vincent Rivasseau,
-- "Trees, Forests and Jungles: A Botanical Garden for Cluster Expansions",
-- in Constructive Physics, Lecture Notes in Physics 446 (1995), 7--36.
-- DOI: 10.1007/3-540-59190-7_20. arXiv:hep-th/9409094.
--
-- These tree/forest identities calibrate the positive tree-resummation shape.
-- They are NOT the authority for the CMP99 domain-comparison cancellation.
-- In the source-native Yang--Mills proof, common generalized-walk terms cancel
-- because the paired restricted background data agree on the common region.
-- Only the surviving walks reach the marked domain discrepancy.
--
-- SHARP FRONTIER
--
-- The remaining Yang--Mills-specific analytic theorem is therefore NOT
-- "prove marked exponential decay" in general.  It is the second-variation
-- inheritance theorem:
--
--   published marked propagator/substituted-background decay
--       + analytic stability of D^2 E under that substitution
--       + CMP116 residual tree/localization summability
--   ----------------------------------------------------------
--       marked exponential decay of the SAME decoupled activity Hessian
--       entering the unified RG norm.
--
-- The existing modules
--
--   BalabanDecoupledActivityHessian
--   BalabanMarkedPolarisationResummation
--
-- already construct respectively the Cauchy-coefficient lift and the finite
-- common-walk cancellation/resummation.  Thus the irreducible physical input
-- is the marked substituted-background stability estimate for D^2 E while
-- retaining BOTH discrepancy-distance and tree-length decay.
------------------------------------------------------------------------

open import DASHI.Physics.YangMills.CompactLieProofLevel

-- Published/source-owned zeroth-order marked background-propagator decay.
cmp99BackgroundPropagatorMarkedDifferenceLevel : ProofLevel
cmp99BackgroundPropagatorMarkedDifferenceLevel = standardImported

-- Published/source-owned use of generalized random-walk localization inside
-- the fluctuation-field cluster expansion.
cmp116GeneralizedRandomWalkClusterLocalisationLevel : ProofLevel
cmp116GeneralizedRandomWalkClusterLocalisationLevel = standardImported

-- Standard connected-graph/tree/forest resummation technology.  This is
-- deliberately separate from the source-native common-domain cancellation.
treeForestResummationCalibrationLevel : ProofLevel
treeForestResummationCalibrationLevel = standardImported

-- Already constructed in-repo: finite-polydisc/Cauchy lift of a pointwise
-- marked substituted-background Hessian bound to the differentiated activity
-- coefficient, followed by common-walk cancellation and finite resummation.
differentiatedCoefficientAndFiniteResummationLevel : ProofLevel
differentiatedCoefficientAndFiniteResummationLevel = machineChecked

-- TRUE remaining physical Lemma 7 primitive.
--
-- Prove on the literal CMP109/CMP116 substituted background that the second
-- field variation is Lipschitz/analytic with a majorant preserving the source
-- marked-distance decay and the residual positive tree-length exponent.
physicalMarkedSubstitutedBackgroundSecondVariationStabilityLevel : ProofLevel
physicalMarkedSubstitutedBackgroundSecondVariationStabilityLevel = conditional

-- Once the preceding physical primitive is instantiated on the SAME activity,
-- the existing resummation + exponential-shell modules produce the weighted
-- quasi-local Hessian row used by the Polchinski/finite-speed route.
physicalMarkedDifferentiatedActivityExponentialLocalisationLevel : ProofLevel
physicalMarkedDifferentiatedActivityExponentialLocalisationLevel = conditional
