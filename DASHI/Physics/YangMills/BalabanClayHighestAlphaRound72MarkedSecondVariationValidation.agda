module DASHI.Physics.YangMills.BalabanClayHighestAlphaRound72MarkedSecondVariationValidation where

------------------------------------------------------------------------
-- ROUND72 FOCUSED ROOT
--
-- Highest-alpha refinement of Lemmas 7--8:
--
--   published CMP99(3) marked propagator/domain decay
--      + CMP109 ALREADY-DIFFERENTIATED E^(2) tree representation
--      + factorwise ordinary/marked OPERATOR estimates
--      + OWNED noncommutative marked-product telescope
--      + CMP116 generalized-walk/tree resummation
--   ---------------------------------------------------------------
--      marked differentiated-activity exponential localization
--      -> dyadic / (3/2)-weighted Hessian row
--      -> multiscale curvature
--      -> compact-Lie Langevin commutator
--         = symmetric Hessian + onsite skew connection
--      -> skew connection contributes zero quadratic derivative energy
--      -> quasi-local propagation -> spatial clustering -> OS gap.
--
-- CMP109 has already taken the two external field variations by the active
-- localization step.  Generic Cauchy machinery remains a fallback, not the
-- primary source-native proof.  Likewise the CMP109 tree factors are generally
-- operator/multilinear compositions, so the noncommutative telescope is the
-- source-faithful primary assembly; the scalar telescope is only calibration.
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
-- Brian C. Hall,
-- "Lie Groups, Lie Algebras, and Representations: An Elementary Introduction",
-- second edition, GTM 222, Springer (2015).
-- DOI: 10.1007/978-3-319-13467-3.
-- Calibration for the compact-Lie bi-invariant metric / adjoint geometry.
--
-- TREE/FOREST CROSS-CHECKS
--
-- David C. Brydges and Paul Federbush,
-- "A New Form of the Mayer Expansion in Classical Statistical Mechanics",
-- J. Math. Phys. 19 (1978), 2064--2067. DOI: 10.1063/1.523586.
--
-- David C. Brydges and Thomas Kennedy,
-- "Mayer Expansions and the Hamilton-Jacobi Equation",
-- J. Stat. Phys. 48 (1987), 19--49. DOI: 10.1007/BF01010398.
--
-- Abdelmalek Abdesselam and Vincent Rivasseau,
-- "Trees, Forests and Jungles: A Botanical Garden for Cluster Expansions",
-- Lecture Notes in Physics 446 (1995), 7--36.
-- DOI: 10.1007/3-540-59190-7_20. arXiv:hep-th/9409094.
--
-- Guardrail: BBF/Brydges--Kennedy/forest formulae calibrate connected
-- graph/tree resummation only.  They do not justify CMP99 common-domain walk
-- cancellation; that equality comes from paired restricted background data.
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
import DASHI.Physics.YangMills.CompactLieLangevinSkewConnectionCancellationExact

round72PublishedMarkedPropagatorDecayLevel : ProofLevel
round72PublishedMarkedPropagatorDecayLevel = standardImported

round72PublishedDifferentiatedActivityTreeStructureLevel : ProofLevel
round72PublishedDifferentiatedActivityTreeStructureLevel = standardImported

round72PublishedGeneralizedWalkClusterLocalisationLevel : ProofLevel
round72PublishedGeneralizedWalkClusterLocalisationLevel = standardImported

-- Source-faithful noncommutative finite product assembly.
round72NoncommutativeMarkedOperatorAssemblyLevel : ProofLevel
round72NoncommutativeMarkedOperatorAssemblyLevel = machineChecked

-- Scalar product assembly remains an exact shadow/calibration.
round72ScalarMarkedProductAssemblyLevel : ProofLevel
round72ScalarMarkedProductAssemblyLevel = machineChecked

round72FiniteMarkedWalkResummationLevel : ProofLevel
round72FiniteMarkedWalkResummationLevel = machineChecked

round72ExponentialShellToWeightedRowLevel : ProofLevel
round72ExponentialShellToWeightedRowLevel = machineChecked

-- Standard compact-Lie connection geometry + owned skew quadratic cancellation.
round72CompactLieAdSkewGeometryLevel : ProofLevel
round72CompactLieAdSkewGeometryLevel = standardImported

round72SkewConnectionQuadraticCancellationLevel : ProofLevel
round72SkewConnectionQuadraticCancellationLevel = machineChecked

------------------------------------------------------------------------
-- TRUE REMAINING LEMMA 7 PRIMITIVE
--
-- On every literal OPERATOR/multilinear factor in CMP109 (4.3)--(4.5), prove
--
--   ||factor_Ω||                  <= b_i,
--   ||factor_Ω'||                 <= b_i,
--   ||factor_Ω - factor_Ω'||      <= m_i,
--
-- where the marked difference m_i inherits CMP99(3) distance-to-change decay
-- and the ordinary b_i retain enough CMP109 tree decay that the noncommutative
-- telescoping majorant has a positive residual localization exponent after
-- CMP116 resummation.
--
-- Existing theorems then construct the whole differentiated tree-product bound,
-- marked E^(2) shell, and weighted quasi-local Hessian row automatically.
------------------------------------------------------------------------

round72PhysicalCMP109MarkedOperatorFactorBoundsLevel : ProofLevel
round72PhysicalCMP109MarkedOperatorFactorBoundsLevel = conditional

------------------------------------------------------------------------
-- SHARPENED LEMMA 8 SEAMS
--
-- (A) identify the SAME Balaban effective density/covariance path with the
--     Bauerschmidt--Bodineau Polchinski C_t, dot C_t, ddot C_t and prove the
--     multiscale curvature/debt inequality from the weighted Hessian row;
--
-- (B) identify the literal compact-group lattice Langevin commutator in a
--     bi-invariant frame.  Once that identity is proved, the connection part is
--     onsite skew and its quadratic derivative-energy contribution is already
--     zero by CompactLieLangevinSkewConnectionCancellationExact.  Therefore no
--     new symmetric growth budget beyond the SAME Hessian is required.
------------------------------------------------------------------------

round72PhysicalSameDensityPolchinskiCurvatureLevel : ProofLevel
round72PhysicalSameDensityPolchinskiCurvatureLevel = conditional

round72PhysicalLiteralCompactLieLangevinCommutatorLevel : ProofLevel
round72PhysicalLiteralCompactLieLangevinCommutatorLevel = conditional

-- After (A)+(B), weighted Gronwall + temporal relaxation are standard analysis;
-- the existing clustering/OS chain consumes their spatial covariance output.
round72PhysicalWeightedPropagationSameFamilyLevel : ProofLevel
round72PhysicalWeightedPropagationSameFamilyLevel = conditional
