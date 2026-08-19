module DASHI.Physics.YangMills.BalabanClayHighestAlphaRound72MarkedSecondVariationValidation where

------------------------------------------------------------------------
-- ROUND72 FOCUSED ROOT
--
-- Highest-alpha refinement of Lemma 7:
--
--   published CMP99(3) marked propagator decay
--      + CMP116 generalized-walk localization
--      + SAME substituted-background second-variation stability
--      + already-owned Cauchy coefficient lift / surviving-walk resummation
--   -------------------------------------------------------------------
--      marked differentiated-activity exponential localization
--      -> dyadic / (3/2)-weighted Hessian row
--      -> multiscale curvature + quasi-local propagation
--      -> spatial clustering -> OS Hamiltonian gap.
--
-- The published zeroth-order marked decay is no longer counted as new
-- Yang--Mills mathematics.  The irreducible live primitive is the inheritance
-- of that decay by D^2 E on the literal CMP109/CMP116 substituted background,
-- while retaining the residual tree-length exponent needed for summability.
--
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
-- Abdelmalek Abdesselam and Vincent Rivasseau,
-- "Trees, Forests and Jungles: A Botanical Garden for Cluster Expansions",
-- Lecture Notes in Physics 446 (1995), 7--36.
-- DOI: 10.1007/3-540-59190-7_20. arXiv:hep-th/9409094.
--
-- Guardrail: BBF/Brydges--Kennedy/forest formulae calibrate connected
-- graph-to-tree resummation.  They are NOT used to justify the source-native
-- equality of paired common-domain walk contributions; that cancellation
-- comes from equality of the restricted background data on the common region.
------------------------------------------------------------------------

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanClayHighestAlphaRound70PolchinskiFiniteSpeedValidation
import DASHI.Physics.YangMills.BalabanMarkedHessianPublishedDecayBoundaryExact
import DASHI.Physics.YangMills.BalabanDecoupledActivityHessian
import DASHI.Physics.YangMills.BalabanMarkedPolarisationResummation
import DASHI.Physics.YangMills.BalabanExponentialToDyadicShellCoarseningExact
import DASHI.Physics.YangMills.BalabanSourceExponentialToWeightedHessianExact

-- Published/source-owned inputs are now named explicitly rather than hidden
-- inside the physical Lemma 7 count.
round72PublishedMarkedPropagatorDecayLevel : ProofLevel
round72PublishedMarkedPropagatorDecayLevel = standardImported

round72PublishedGeneralizedWalkClusterLocalisationLevel : ProofLevel
round72PublishedGeneralizedWalkClusterLocalisationLevel = standardImported

-- In-repo theorem-producing algebra already closes the Cauchy coefficient
-- lift, finite common-walk cancellation, resummation, exponential->dyadic
-- shell conversion, and direct exponential->weighted-row conversion.
round72DifferentiatedCoefficientLiftLevel : ProofLevel
round72DifferentiatedCoefficientLiftLevel = machineChecked

round72FiniteMarkedWalkResummationLevel : ProofLevel
round72FiniteMarkedWalkResummationLevel = machineChecked

round72ExponentialShellToWeightedRowLevel : ProofLevel
round72ExponentialShellToWeightedRowLevel = machineChecked

------------------------------------------------------------------------
-- TRUE REMAINING LEMMA 7 PRIMITIVE
--
-- On the literal CMP116 nonlinear substituted background H_k(s(Y_0),B'),
-- prove that the second field variation of the SAME CMP109 local activity is
-- stable under a marked domain/background change with a majorant preserving
-- both:
--
--   (i) the distance-to-nearest-change exponential inherited from CMP99(3),
--   (ii) the residual positive tree/localization exponent used by CMP116.
--
-- Schematically the target is
--
-- |D^2 E_Ω(X;x,y) - D^2 E_Ω'(X;x,y)|
--   <= C exp(-δ |x-y|)
--        exp(-κ tree(X))
--        exp(-δ0 D(Ω,Ω';x,y)).
--
-- Once this is instantiated, existing modules construct the complete marked
-- Hessian shell and weighted quasi-local influence row.  There is no further
-- independent "prove Hessian quasi-locality" lemma on this route.
------------------------------------------------------------------------

round72PhysicalMarkedSecondVariationInheritanceLevel : ProofLevel
round72PhysicalMarkedSecondVariationInheritanceLevel = conditional

-- Downstream same-object identifications still required for the full mass-gap
-- role: Polchinski covariance/curvature on the same effective density and the
-- compact-group Langevin derivative generator controlled by this Hessian.
round72PhysicalSameDensityPolchinskiCurvatureLevel : ProofLevel
round72PhysicalSameDensityPolchinskiCurvatureLevel = conditional

round72PhysicalCompactGroupDerivativePropagationLevel : ProofLevel
round72PhysicalCompactGroupDerivativePropagationLevel = conditional
