module DASHI.Physics.YangMills.BalabanMarkedHessianPublishedDecayBoundaryExact where

------------------------------------------------------------------------
-- ROUND72: PUBLISHED MARKED PROPAGATOR DECAY != DIFFERENTIATED E^(2) CLOSURE
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
-- Equations (4.3)--(4.5) express the ALREADY DIFFERENTIATED local activity in
-- terms of background-map derivatives/tree expressions; (4.35) is the n=2
-- specialization and (4.37) resums E^(2) to the polarization tensor.  Hence
-- the primary proof route does not need to obtain the Hessian through a new
-- generic Cauchy-radius argument.
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. II.
-- Cluster Expansions", Communications in Mathematical Physics 116(1) (1988),
-- 1--22. DOI: 10.1007/BF01239022.
-- CMP116 explicitly constructs the fluctuation-field cluster expansion using
-- generalized random-walk expansions for propagators/minimizers and supplies
-- the residual localization/tree summability used after the marked comparison.
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
-- These tree/forest identities calibrate connected-graph/tree resummation.
-- They are NOT the authority for the CMP99 common-domain cancellation.  In the
-- source-native Yang--Mills proof, paired generalized-walk terms cancel because
-- the restricted background data agree on their common localization region.
--
-- SHARP FRONTIER
--
-- The remaining Yang--Mills-specific analytic theorem is NOT "prove marked
-- exponential decay" from scratch and NOT "derive D^2 by generic Cauchy".
-- CMP109 has already differentiated.  The true primitive is:
--
--   one factor in the CMP109 (4.3) differentiated tree expression
--       -> replace that factor by its CMP99(3) marked domain difference
--       -> keep every unchanged factor under the ordinary CMP109 tree bound
--       -> retain BOTH marked distance and residual tree-length decay
--       -> telescope the finite factor replacement
--       -> apply CMP116 localization/tree summability.
--
-- The repository already owns the finite replacement telescope and the finite
-- surviving-walk cancellation/resummation.  Therefore the irreducible physical
-- input is the SOURCE-NATIVE TERMWISE marked replacement bound for the literal
-- E^(2) tree factors, with its normalization/history dependence checked on the
-- same effective action.
------------------------------------------------------------------------

open import DASHI.Physics.YangMills.CompactLieProofLevel

-- Published/source-owned marked background-propagator decay.
cmp99BackgroundPropagatorMarkedDifferenceLevel : ProofLevel
cmp99BackgroundPropagatorMarkedDifferenceLevel = standardImported

-- Published/source-owned already-differentiated E^(2) tree/locality structure.
cmp109DifferentiatedActivityTreeStructureLevel : ProofLevel
cmp109DifferentiatedActivityTreeStructureLevel = standardImported

-- Published/source-owned generalized-walk cluster localization and residual
-- tree summability.
cmp116GeneralizedRandomWalkClusterLocalisationLevel : ProofLevel
cmp116GeneralizedRandomWalkClusterLocalisationLevel = standardImported

-- Standard connected-graph/tree/forest resummation technology.  Kept separate
-- from Bałaban's source-native common-domain cancellation.
treeForestResummationCalibrationLevel : ProofLevel
treeForestResummationCalibrationLevel = standardImported

-- Already constructed in-repo: finite factor telescope / triangle inequality,
-- finite common-walk cancellation, marked surviving-walk resummation, and
-- exponential-shell -> dyadic/weighted-row algebra.
finiteDifferentiatedReplacementAndResummationLevel : ProofLevel
finiteDifferentiatedReplacementAndResummationLevel = machineChecked

-- Generic finite-polydisc/Cauchy coefficient machinery remains available as a
-- fallback/check, but it is NOT the primary source-native route because CMP109
-- has already taken the two external field variations before (4.35)/(4.37).
genericCauchyDifferentiationFallbackLevel : ProofLevel
genericCauchyDifferentiationFallbackLevel = machineChecked

-- TRUE remaining physical Lemma 7 primitive.
--
-- For every replacement term in the literal CMP109 differentiated tree
-- expression, prove the bound obtained by inserting ONE CMP99(3) marked
-- propagator/background-difference factor and ordinary decay bounds on all
-- unchanged factors, without sacrificing the remaining positive tree exponent.
physicalDifferentiatedMarkedReplacementTermBoundLevel : ProofLevel
physicalDifferentiatedMarkedReplacementTermBoundLevel = conditional

-- Once that termwise primitive is instantiated, existing finite telescope +
-- CMP116 resummation modules produce the complete marked E^(2) exponential
-- localization and hence the weighted quasi-local Hessian row.
physicalMarkedDifferentiatedActivityExponentialLocalisationLevel : ProofLevel
physicalMarkedDifferentiatedActivityExponentialLocalisationLevel = conditional
