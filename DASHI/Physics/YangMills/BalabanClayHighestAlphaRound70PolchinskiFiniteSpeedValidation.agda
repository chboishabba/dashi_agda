module DASHI.Physics.YangMills.BalabanClayHighestAlphaRound70PolchinskiFiniteSpeedValidation where

------------------------------------------------------------------------
-- ROUND70 FOCUSED ROOT: L7 -> MULTISCALE CURVATURE -> FINITE SPEED -> OS GAP
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
-- 1. The Polchinski source criterion is now the literal covariance form
--
--      dotC Hess(V_t) dotC - 1/2 ddotC >= dotEll dotC,
--
--    not a silently specialised bare/smoothed Hessian condition.
--
-- 2. Rooted KP + the unified derivative shell estimate gives a volume-uniform
--    Hessian row budget.  The 17/32 recurrence makes its negative curvature
--    debt summable with the exact 32/15 factor.
--
-- 3. Local derivative propagation is no longer an opaque premise at its
--    combinatorial core.  A finite local influence generator has
--
--      (A^n)_{xy}=0
--
--    whenever no n-step local walk connects x to y.  Thus all Dyson orders
--    below graph distance vanish exactly.
--
-- 4. A nonnegative influence majorant with row mass rho has power row masses
--    controlled by rho^n.  Hence the same local Hessian/KP constant controls
--    propagation amplitude at every order once the physical derivative
--    generator is identified with/dominated by the action Hessian.
--
-- 5. Temporal relaxation e^{-lambda t} and finite-speed leakage
--    e^{v t-mu d} balance at
--
--      t = mu d/(lambda+v),
--      m = lambda mu/(lambda+v).
--
--    This rate is exact rational algebra before any analytic exponential
--    estimate is inserted.
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

-- One local derivative coordinate feeds Hessian / curvature.
import DASHI.Physics.YangMills.BalabanRootedKPToHessianRowBudgetExact
import DASHI.Physics.YangMills.BalabanFiniteHessianRowSumQuadraticBoundExact
import DASHI.Physics.YangMills.BalabanUnifiedPolchinskiCurvatureDebtExact
import DASHI.Physics.YangMills.BalabanPolchinskiMultiscaleLSIBridgeExact

-- Finite-speed theorem-producing core.
import DASHI.Physics.YangMills.BalabanFiniteSpeedLocalInfluencePathExact
import DASHI.Physics.YangMills.BalabanFiniteInfluenceRowMassPowerExact
import DASHI.Physics.YangMills.BalabanPoincareFiniteSpeedClusteringRateExact
import DASHI.Physics.YangMills.BalabanStochasticFiniteSpeedSpatialClusteringExact

-- Physical spectral endpoint after actual spatial/Euclidean clustering.
import DASHI.Physics.YangMills.BalabanClayT5ClusteringToTransferGapExact
import DASHI.Physics.YangMills.BalabanClayT5PhysicalContinuumOSGapBridgeExact

round70FiniteSpeedLocalityPowerCancellationLevel : ProofLevel
round70FiniteSpeedLocalityPowerCancellationLevel = machineChecked

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
-- P2. Identify the derivative evolution generator of that same stochastic
--     dynamics.  For Langevin form its off-diagonal influence is the action
--     Hessian; prove the literal lattice/gauge calculus and dominate its
--     absolute row mass by the rooted KP derivative budget.
--
-- P3. Prove the analytic high-order Dyson/semigroup tail from that row mass.
--     The lower orders are already exactly zero by graph distance.
--
-- P4. Use the resulting physical exponential spatial covariance envelope in
--     the SAME continuum/OS family.  Existing OS spectral machinery then gives
--     the physical Hamiltonian gap; no auxiliary Markov gap is substituted.
--
-- These are coordinates of the strong all-scale RG theorem, not four new Clay
-- package labels.
------------------------------------------------------------------------

round70PhysicalMultiscaleCurvatureInstantiationLevel : ProofLevel
round70PhysicalMultiscaleCurvatureInstantiationLevel = conditional

round70PhysicalDerivativeGeneratorHessianIdentificationLevel : ProofLevel
round70PhysicalDerivativeGeneratorHessianIdentificationLevel = conditional

round70PhysicalHighOrderSemigroupTailLevel : ProofLevel
round70PhysicalHighOrderSemigroupTailLevel = conditional

round70PhysicalSameFamilySpatialClusteringLevel : ProofLevel
round70PhysicalSameFamilySpatialClusteringLevel = conditional
