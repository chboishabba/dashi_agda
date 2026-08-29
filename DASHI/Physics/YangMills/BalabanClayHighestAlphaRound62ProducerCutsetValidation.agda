module DASHI.Physics.YangMills.BalabanClayHighestAlphaRound62ProducerCutsetValidation where

------------------------------------------------------------------------
-- ROUND62 HIGHEST-ALPHA PRODUCER CUTSET
--
-- This root is intentionally a CUTSET correction, not a new receipt layer.
-- It imports the exact Round61 carrier mathematics and records only changes
-- forced by theorem-level results already present on the live branch.
--
-- G2 CORRECTION
--
-- The proposed three-estimate split
--
--   source D1 norm + defect D1 norm + raw aggregate
--
-- is not merely suboptimal: it is falsified.  On the literal plaquette carrier
--
--   3 ||w_1||^2 = C_p,
--
-- so separate polarization spends 1/6 C_p, whereas the entire selected
-- singleton headroom is 55/18874368 C_p.  The live object therefore remains
-- signed before majorisation:
--
--   R_corr = (R1-G11) + (R2+R3+R4).
--
-- Existing Round61 modules reduce the G2 frontier to exactly TWO physical
-- charge-relative enclosures, one for each summand above.  No raw K+ row norm
-- and no LBB constant is needed on this route.
--
-- REDUCED GHOST CORRECTION
--
-- Nicholas J. Higham,
-- "Functions of Matrices: Theory and Computation", SIAM, 2008.
-- DOI: 10.1137/1.9780898717778.
--
-- L. D. Faddeev and V. N. Popov,
-- "Feynman Diagrams for the Yang-Mills Field", Physics Letters B 25 (1967),
-- 29--30. DOI: 10.1016/0370-2693(67)90067-6.
--
-- The physical reduced relative matrix satisfies rowMass(R_A)<1/5.  The branch
-- already constructs its literal alternating matrix-log tail and shifted
-- geometric Cauchy modulus.  Round62 additionally pushes that signed recursion
-- through the finite trace.  The remaining principal-log / log-det identity is
-- standard finite functional calculus on the disk |z-1|<1/5, not a Yang--Mills
-- research producer.
--
-- OS / MASS-GAP CORRECTION
--
-- Konrad Osterwalder and Robert Schrader,
-- "Axioms for Euclidean Green's Functions", CMP 31 (1973), 83--112.
-- DOI: 10.1007/BF01645738.
--
-- Konrad Osterwalder and Robert Schrader,
-- "Axioms for Euclidean Green's Functions II", CMP 42 (1975), 281--305.
-- DOI: 10.1007/BF01608978.
--
-- O. Penrose and J. L. Lebowitz,
-- "On the Exponential Decay of Correlation Functions", CMP 39 (1974),
-- 165--184. DOI: 10.1007/BF01614239.
--
-- Once the continuum OS reconstruction and physical uniform exponential
-- clustering are present, the Hamiltonian spectral gap is a standard
-- Laplace-support/spectral-calculus closure.  It is therefore removed from the
-- hard physical producer count.
--
-- LIVE SU(2) HARD PRODUCERS
--
-- A. signed G2                                      2
--    A1  selected correlated D1 = R1-G11 enclosure
--    A2  selected raw higher R2+R3+R4 enclosure
--
-- B. literal Wilson + ghost + Haar one loop         1
--    B1  positive literal one-loop coefficient
--
-- C. nonlinear physical RG                          1
--    C1  uniform physical quartic remainder
--
-- D. literal transfer                               2
--    D1  Wilson kernel naturality on the same carrier
--    D2  temporal trace/integration naturality
--
-- E. uniform lattice spectral gap                   2
--    E1  terminal physical Wilson transfer gap
--    E2  cutoff-uniform physical Feshbach loss budget
--
-- F. continuum construction                         3
--    F1  renormalized Schwinger scale increment
--    F2  Yang--Mills Schwinger tightness
--    F3  unique OS-stable continuum limit
--
-- G. continuum nontriviality / mass scale           2
--    G1  physical fourth-cumulant lower bound
--    G2  physical uniform exponential clustering
--
-- TOTAL: 2+1+1+2+2+3+2 = 13 genuinely hard SU(2) physical producers.
--
-- Supporting finite algebra, source-to-carrier identifications, the principal
-- matrix logarithm/log-determinant theorem, and clustering-to-Hamiltonian-gap
-- are implementation obligations or standard mathematics, not separate
-- physical research risks.
--
-- COMPACT SIMPLE G
-- A later group-uniformity campaign is still required for the full arbitrary
-- compact-simple-group Clay formulation.  The existing Casimir/Dynkin trace
-- identity removes Lie-algebra bookkeeping but not group-uniform analytic
-- constants.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanClayHighestAlphaRound61DLRTransferAuditValidation

-- G2 falsifier + live signed compiler.
import DASHI.Physics.YangMills.BalabanPlaquetteBoundaryStateNormChargeExact
import DASHI.Physics.YangMills.BalabanDegreeOneStateNormG2HeadroomNoGoExact
import DASHI.Physics.YangMills.BalabanCanonicalCorrelatedDegreeOneBeforePolarizationExact
import DASHI.Physics.YangMills.BalabanChargeRelativeCorrelatedD1G2ClosureExact

-- Ghost finite trace/log closure.
import DASHI.Physics.YangMills.BalabanReducedGhostSignedMatrixLogTailExact
import DASHI.Physics.YangMills.BalabanReducedGhostSignedTraceTailExact
import DASHI.Physics.YangMills.BalabanReducedGhostTraceFastCauchyCompletionExact

-- One-loop exact symmetry reduction + normalization sanity.
import DASHI.Physics.YangMills.BalabanCMP109WalshFiniteModeFourRepresentativeLowerExact
import DASHI.Physics.YangMills.BalabanSU2OneLoopNormalizationSanityExact

-- OS clustering -> spectral-gap standard closure.
import DASHI.Physics.YangMills.BalabanOSExponentialClusteringImpliesHamiltonianGapExact

-- Transfer, continuum and non-Gaussian endpoint carriers.
import DASHI.Physics.YangMills.BalabanWilsonTransferIntertwinerExact
import DASHI.Physics.YangMills.BalabanTransferKernelTraceNaturalityExact
import DASHI.Physics.YangMills.BalabanContinuumProkhorovSubsequenceExact
import DASHI.Physics.YangMills.BalabanContinuumScaleLocalObservableCauchyExact
import DASHI.Physics.YangMills.YangMillsContinuumFourthCumulantNonGaussianExact
import DASHI.Physics.YangMills.YangMillsCompactSimpleCasimirDynkinTraceExact

------------------------------------------------------------------------
-- Executable cutset arithmetic.
------------------------------------------------------------------------

g2Hard oneLoopHard nonlinearRGHard transferHard latticeGapHard continuumHard
  nontrivialityMassHard : Nat
g2Hard = 2
oneLoopHard = 1
nonlinearRGHard = 1
transferHard = 2
latticeGapHard = 2
continuumHard = 3
nontrivialityMassHard = 2

liveSU2HardProducerCount : Nat
liveSU2HardProducerCount =
  g2Hard + oneLoopHard + nonlinearRGHard + transferHard + latticeGapHard
  + continuumHard + nontrivialityMassHard

liveSU2HardProducerCountExact : liveSU2HardProducerCount ≡ 13
liveSU2HardProducerCountExact = refl

round62CutsetArithmeticLevel : ProofLevel
round62CutsetArithmeticLevel = machineChecked

ghostPrincipalLogDeterminantFunctionalCalculusLevel : ProofLevel
ghostPrincipalLogDeterminantFunctionalCalculusLevel = standardImported

osExponentialClusteringToHamiltonianGapLevel : ProofLevel
osExponentialClusteringToHamiltonianGapLevel = standardImported

-- The hard frontier is now thirteen physical producers, not fourteen and not
-- the earlier twenty-one named endpoints.
liveSU2ThirteenPhysicalProducerCutsetLevel : ProofLevel
liveSU2ThirteenPhysicalProducerCutsetLevel = conditional
