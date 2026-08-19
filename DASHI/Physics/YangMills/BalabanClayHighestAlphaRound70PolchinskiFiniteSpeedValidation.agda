module DASHI.Physics.YangMills.BalabanClayHighestAlphaRound70PolchinskiFiniteSpeedValidation where

------------------------------------------------------------------------
-- ROUND71 FOCUSED ROOT: L7 -> SOURCE MARKED HESSIAN -> MULTISCALE CURVATURE
--                         -> QUASI-LOCAL PROPAGATION -> SPATIAL CLUSTERING
--                         -> OS GAP
--
-- This root is not a new receipt count.  It records the shortest current
-- theorem-producing dependency path from the unified physical RG estimate to
-- the Clay mass-gap role while preserving the same-object boundaries.
--
-- PRIMARY SOURCES / CALIBRATION
--
-- Roland Bauerschmidt and Thierry Bodineau,
-- "Log-Sobolev Inequality for the Continuum Sine-Gordon Model",
-- Communications on Pure and Applied Mathematics 74 (2021), 2064--2113.
-- DOI: 10.1002/cpa.21926. arXiv:1907.12308.
--
-- Roland Bauerschmidt, Thierry Bodineau and Benoit Dagallier,
-- "Stochastic dynamics and the Polchinski equation: an introduction",
-- Probability Surveys 21 (2024), 200--290.
-- DOI: 10.1214/24-PS27.
--
-- Jordan Serres,
-- "Behavior of the Poincare constant along the Polchinski renormalization
-- flow", arXiv:2208.08186.  No DOI recorded here.
--
-- Hao Shen, Rongchan Zhu and Xiangchan Zhu,
-- "A Stochastic Analysis Approach to Lattice Yang--Mills at Strong Coupling",
-- Communications in Mathematical Physics 400 (2023), 805--851.
-- DOI: 10.1007/s00220-022-04609-1. arXiv:2204.12737.
--
-- Ali Naddaf and Thomas Spencer,
-- "On Homogenization and Scaling Limit of Some Gradient Perturbations of a
-- Massless Free Field", Communications in Mathematical Physics 183 (1997),
-- 55--84. DOI: 10.1007/s002200050020.
--
-- Konrad Osterwalder and Robert Schrader,
-- "Axioms for Euclidean Green's Functions", CMP 31 (1973), 83--112.
-- DOI: 10.1007/BF01645738.
-- "Axioms for Euclidean Green's Functions II", CMP 42 (1975), 281--305.
-- DOI: 10.1007/BF01608978.
--
-- SOURCE-NATIVE BALABAN LOCALISATION CHAIN
--
-- Tadeusz Bałaban,
-- "Propagators and Renormalization Transformations for Lattice Gauge
-- Theories. I", CMP 95 (1984), 17--40. DOI: 10.1007/BF01215753.
--
-- Tadeusz Bałaban,
-- "Propagators and Renormalization Transformations for Lattice Gauge
-- Theories. II", CMP 96 (1984), 223--250. DOI: 10.1007/BF01240221.
--
-- IMPORTANT: there are TWO distinct Bałaban papers in CMP volume 99.
--
-- (a) "Spaces of Regular Gauge Field Configurations on a Lattice and Gauge
--     Fixing Conditions", CMP 99(1) (1985), 75--102.
--     DOI: 10.1007/BF01466594.
--     Role here: regular gauge chart / gauge-fixing domain.
--
-- (b) "Propagators for Lattice Gauge Theories in a Background Field",
--     CMP 99(3) (1985), 389--434. DOI: 10.1007/BF01240355.
--     Role here: background-propagator random-walk localisation and the
--     Theorem 3.14 / equation (3.154) marked domain-sequence comparison.
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I.
-- Generation of Effective Actions in a Small Field Approximation and a
-- Coupling Constant Renormalization in Four Dimensions",
-- CMP 109 (1987), 249--301. DOI: 10.1007/BF01215223.
-- Role here: twice-differentiated local activity / polarization and its
-- resummed exponential kernel decay.
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. II.
-- Cluster Expansions", CMP 116(1) (1988), 1--22.
-- DOI: 10.1007/BF01239022.
-- Role here: residual localization/tree summability after the marked
-- background-propagator comparison.
--
-- ADVERSARIAL CLAIM BOUNDARY
--
-- The 2026 Watt et al. dissolution manuscript publicly describes a proof
-- sketch for an all-finite-beta lattice gap by combining BBD-type multiscale
-- functional inequalities with SZZ dynamics.  It explicitly does not claim a
-- Clay solution.  No theorem from that manuscript is imported here.  Its only
-- current value is methodological cross-check: the same BBD+SZZ synthesis is
-- independently reached below, but every Yang--Mills-specific premise remains
-- to be proved on the literal Balaban effective density.
--
-- ROUND71 SHARPENING
--
-- 1. The Polchinski source criterion is the literal covariance form
--
--      dotC Hess(V_t) dotC - 1/2 ddotC >= dotEll dotC,
--
--    not a silently specialised bare/smoothed Hessian condition.
--
-- 2. The physical Hessian-shell input is no longer an invented quasi-locality
--    receipt.  The intended source path is now explicit:
--
--      CMP99(3) marked background-propagator difference
--        -> CMP109 twice-differentiated local activity/polarization
--        -> CMP116 marked/tree resummation
--        -> positive exponential shell rate
--        -> one shell-width comparison exp(-delta R) <= 1/2
--        -> dyadic h_d <= c_H s_d.
--
-- 3. Rooted KP + that derivative shell estimate gives BOTH
--
--      unweighted Hessian row <= c_H/2,
--
--    and, more importantly for the RG effective action,
--
--      sum_d (3/2)^d h_d <= c_H.
--
--    The second theorem uses the exact identity
--
--      (3/2)^d (1/2)^d = (3/4)^d,
--      (1/4) sum_d (3/4)^d = 1.
--
--    This is the correct quasi-local influence norm: the renormalised polymer
--    action is exponentially decaying, not strictly finite-range.
--
-- 4. The exact local-walk theorem is retained as a useful SPECIAL CASE for the
--    bare/local Wilson part.  It is not promoted to the full effective action.
--
-- 5. Weighted propagation with distance weight 3/2 has the expected form
--
--      exp(c_H t) (3/2)^(-d)
--        = exp(c_H t - log(3/2) d).
--
--    Against temporal relaxation exp(-lambda t), the exact linear rate balance
--    gives
--
--      m = lambda log(3/2) / (lambda + c_H).
--
-- 6. The stochastic gap is NOT promoted directly to the Clay Hamiltonian gap.
--    Spatial covariance comes first; the existing OS4 spectral theorem then
--    excludes positive subgap modes on the reconstructed Hamiltonian.
------------------------------------------------------------------------

open import DASHI.Physics.YangMills.CompactLieProofLevel

-- Literal endpoint / five-role compiler.
import DASHI.Physics.YangMills.YangMillsClayLiteralTopDownConstructionExact
import DASHI.Physics.YangMills.YangMillsClayTopDownFiveTheoremClosureExact

-- Unified RG contraction and exact summability.
import DASHI.Physics.YangMills.BalabanUnifiedPolymerSchwingerNormExact
import DASHI.Physics.YangMills.BalabanUnifiedPolymerStepVContractionBudgetExact
import DASHI.Physics.YangMills.BalabanUnifiedSeventeenThirtySecondIterationExact
import DASHI.Physics.YangMills.BalabanUnifiedSeventeenThirtySecondTailModulusExact

-- Source-native differentiated marked localisation -> dyadic shell.
import DASHI.Physics.YangMills.BalabanDecoupledActivityHessian
import DASHI.Physics.YangMills.BalabanMarkedPolarisationResummation
import DASHI.Physics.YangMills.BalabanExponentialToDyadicShellCoarseningExact

-- One derivative/KP coordinate feeds curvature AND quasi-local propagation.
import DASHI.Physics.YangMills.BalabanRootedKPToHessianRowBudgetExact
import DASHI.Physics.YangMills.BalabanRootedKPToExponentialWeightedHessianExact
import DASHI.Physics.YangMills.BalabanFiniteHessianRowSumQuadraticBoundExact
import DASHI.Physics.YangMills.BalabanUnifiedPolchinskiCurvatureDebtExact
import DASHI.Physics.YangMills.BalabanPolchinskiMultiscaleLSIBridgeExact

-- Propagation theorem-producing core.
-- Strict locality is a special-case consistency check; weighted quasi-local
-- Hessian control is the main all-scale route.
import DASHI.Physics.YangMills.BalabanFiniteSpeedLocalInfluencePathExact
import DASHI.Physics.YangMills.BalabanFiniteInfluenceRowMassPowerExact
import DASHI.Physics.YangMills.BalabanPoincareFiniteSpeedClusteringRateExact
import DASHI.Physics.YangMills.BalabanStochasticFiniteSpeedSpatialClusteringExact

-- Physical spectral endpoint after actual spatial/Euclidean clustering.
import DASHI.Physics.YangMills.BalabanClayT5ClusteringToTransferGapExact
import DASHI.Physics.YangMills.BalabanClayT5PhysicalContinuumOSGapBridgeExact

round71ExponentialToDyadicShellCompilerLevel : ProofLevel
round71ExponentialToDyadicShellCompilerLevel = machineChecked

round71RootedKPWeightedHessianLevel : ProofLevel
round71RootedKPWeightedHessianLevel = machineChecked

round71BareLocalityPowerCancellationLevel : ProofLevel
round71BareLocalityPowerCancellationLevel = machineChecked

round71FiniteInfluenceRowMassPowerLevel : ProofLevel
round71FiniteInfluenceRowMassPowerLevel = machineChecked

round71RelaxationFiniteSpeedBalanceLevel : ProofLevel
round71RelaxationFiniteSpeedBalanceLevel = machineChecked

round71StochasticToSpatialAssemblyLevel : ProofLevel
round71StochasticToSpatialAssemblyLevel = machineChecked

round71PolchinskiCriterionAuthorityLevel : ProofLevel
round71PolchinskiCriterionAuthorityLevel = standardImported

------------------------------------------------------------------------
-- ACTUAL PHYSICAL FRONTIER ON THIS ROUTE
--
-- P0. Instantiate the source-native CMP99(3)/109/116 marked differentiated
--     activity estimate and identify its exponential shell with the SAME L7
--     Hessian shell.  Choose one coarse shell width R for which the certified
--     source factor exp(-delta R) <= 1/2.  The all-depth dyadic comparison is
--     then already constructed by BalabanExponentialToDyadicShellCoarsening.
--
-- P1. Instantiate the exact dotC/ddotC multiscale curvature inequality on the
--     same Balaban effective density and prove its accumulated negative debt is
--     uniform/summable from L7.
--
-- P2. Prove the literal lattice Langevin derivative commutator: the derivative
--     influence matrix is the action Hessian, with group-connection/gauge terms
--     treated on the actual compact-group manifold.  The SAME P0 shell estimate
--     controls its absolute exponentially weighted row.
--
-- P3. Apply standard weighted Gronwall/semigroup analysis to the resulting
--     quasi-local row bound, obtaining the physical finite-speed envelope
--
--       exp(c_H t) (3/2)^(-distance).
--
-- P4. Combine that with the SAME-measure Polchinski Poincare/LSI temporal rate
--     and pass the resulting exponential Euclidean covariance envelope through
--     the SAME continuum/OS family.  Existing OS spectral machinery then gives
--     the physical Hamiltonian gap; no auxiliary Markov gap is substituted.
--
-- P0/P1/P2 are coordinates of the same strong all-scale RG theorem, not three
-- independent gap receipts.  In particular the one marked differentiated
-- Hessian estimate advances unified norm control, curvature and propagation at
-- once.
------------------------------------------------------------------------

round71PhysicalMarkedDifferentiatedHessianShellLevel : ProofLevel
round71PhysicalMarkedDifferentiatedHessianShellLevel = conditional

round71PhysicalMultiscaleCurvatureInstantiationLevel : ProofLevel
round71PhysicalMultiscaleCurvatureInstantiationLevel = conditional

round71PhysicalDerivativeGeneratorHessianIdentificationLevel : ProofLevel
round71PhysicalDerivativeGeneratorHessianIdentificationLevel = conditional

round71PhysicalWeightedGronwallPropagationLevel : ProofLevel
round71PhysicalWeightedGronwallPropagationLevel = conditional

round71PhysicalSameFamilySpatialClusteringLevel : ProofLevel
round71PhysicalSameFamilySpatialClusteringLevel = conditional
