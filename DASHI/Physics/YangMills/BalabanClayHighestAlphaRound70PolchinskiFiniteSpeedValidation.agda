module DASHI.Physics.YangMills.BalabanClayHighestAlphaRound70PolchinskiFiniteSpeedValidation where

------------------------------------------------------------------------
-- ROUND70 FOCUSED ROOT: L7 -> MULTISCALE CURVATURE -> QUASI-LOCAL PROPAGATION
--                         -> SPATIAL CLUSTERING -> OS GAP
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
-- DOI: 10.1007/s00220-022-04609-1.
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
-- ROUND70 SHARPENING
--
-- 1. The Polchinski source criterion is the literal covariance form
--
--      dotC Hess(V_t) dotC - 1/2 ddotC >= dotEll dotC,
--
--    not a silently specialised bare/smoothed Hessian condition.
--
-- 2. Rooted KP + the unified derivative shell estimate gives BOTH:
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
-- 3. The exact local-walk theorem is retained as a useful SPECIAL CASE for the
--    bare/local Wilson part: if a generator is strictly local, every matrix
--    power below graph distance vanishes.  It is not promoted to the full
--    effective action after RG.
--
-- 4. Finite Fubini/distributivity proves that a nonnegative influence majorant
--    with row mass rho has positive power row masses <= rho^n.  The weighted
--    version is what a quasi-local Gronwall argument consumes.
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
--    The rational balancing theorem is already exact; only the standard
--    exp/log/Gronwall analysis and physical generator identification remain.
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

round70RootedKPWeightedHessianLevel : ProofLevel
round70RootedKPWeightedHessianLevel = machineChecked

round70BareLocalityPowerCancellationLevel : ProofLevel
round70BareLocalityPowerCancellationLevel = machineChecked

round70FiniteInfluenceRowMassPowerLevel : ProofLevel
round70FiniteInfluenceRowMassPowerLevel = machineChecked

round70RelaxationFiniteSpeedBalanceLevel : ProofLevel
round70RelaxationFiniteSpeedBalanceLevel = machineChecked

round70StochasticToSpatialAssemblyLevel : ProofLevel
round70StochasticToSpatialAssemblyLevel = machineChecked

round70PolchinskiCriterionAuthorityLevel : ProofLevel
round70PolchinskiCriterionAuthorityLevel = standardImported

------------------------------------------------------------------------
-- ACTUAL PHYSICAL FRONTIER ON THIS ROUTE
--
-- P1. Instantiate the exact dotC/ddotC multiscale curvature inequality on the
--     same Balaban effective density and prove its accumulated negative debt is
--     uniform/summable from L7.
--
-- P2. Prove the literal lattice Langevin derivative commutator: the derivative
--     influence matrix is the action Hessian (with gauge/connection terms
--     treated on the actual group manifold), and the SAME derivative-shell
--     estimate h_d <= c_H s_d controls its absolute weighted row.
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
-- These are coordinates of the strong all-scale RG theorem, not four new Clay
-- package labels.  In particular P1 and P2 share the SAME L7 derivative/Hessian
-- shell estimate, so proving that estimate advances both curvature and
-- propagation simultaneously.
------------------------------------------------------------------------

round70PhysicalMultiscaleCurvatureInstantiationLevel : ProofLevel
round70PhysicalMultiscaleCurvatureInstantiationLevel = conditional

round70PhysicalDerivativeGeneratorHessianIdentificationLevel : ProofLevel
round70PhysicalDerivativeGeneratorHessianIdentificationLevel = conditional

round70PhysicalWeightedGronwallPropagationLevel : ProofLevel
round70PhysicalWeightedGronwallPropagationLevel = conditional

round70PhysicalSameFamilySpatialClusteringLevel : ProofLevel
round70PhysicalSameFamilySpatialClusteringLevel = conditional
