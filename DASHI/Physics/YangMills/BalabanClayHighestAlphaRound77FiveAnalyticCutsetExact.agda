module DASHI.Physics.YangMills.BalabanClayHighestAlphaRound77FiveAnalyticCutsetExact where

------------------------------------------------------------------------
-- ROUND77: 6 -> 5 INDEPENDENT ANALYTIC JOBS
--
-- Round76 left `InteractingContinuumNontriviality` as a separate sixth job.
-- The structural Gaussian reductio is now opened far enough that no independent
-- fourth-cumulant estimate is needed on the shortest route.
--
-- The key dependency is:
--
--   SameFamilyCompositeOPEStressWardClosure (strengthened)
--       supplies, under a hypothetical Gaussian SAME-family limit,
--       one local O(4)-covariant two-derivative Ward kernel
--                         |
--                         v
--   exact finite coefficient classification
--       m^2 = 0, Z = 1, Y = -1
--                         |
--                         v
--   standard Gaussian OS/Fock reconstruction
--       massless transverse Maxwell one-particle sector on SAME H
--                         |
--                         v
--   SameDensityCompactLieHeatLangevinClustering
--       positive physical spectral gap on SAME H
--                         |
--                         v
--       contradiction -> continuum family is non-Gaussian.
--
-- The coefficient classification is proved in
-- `YangMillsGaussianWardTwoDerivativeMaxwellClassificationExact` and the
-- same-H contradiction compiler is proved in
-- `YangMillsGaussianWardGapNontrivialityExact`.
--
-- IMPORTANT: Gaussianity alone is NOT being promoted to Maxwell. The genuine
-- physical statement "a hypothetical Gaussian limit has the local
-- two-derivative Ward kernel" is explicitly part of job #5 below. That is the
-- correct local-field/Ward theorem, not a hidden sixth analytic estimate.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanOSMassGapClosure as OS
import DASHI.Physics.YangMills.BalabanClayHighestAlphaRound76SixAnalyticCutsetExact
import DASHI.Physics.YangMills.YangMillsContinuumOPEStressWardGaussianKernelExact
import DASHI.Physics.YangMills.YangMillsGaussianWardTwoDerivativeMaxwellClassificationExact
import DASHI.Physics.YangMills.YangMillsGaussianWardGapNontrivialityExact as Nontrivial
import DASHI.Physics.YangMills.SchattenTraceClassCompositePerturbationExact

------------------------------------------------------------------------
-- Exact deletion theorem for old job #6.
--
-- `SameSystemGaussianWardGapData` contains only:
--   * local Gaussian->Ward-kernel data assigned to strengthened job #5;
--   * the positive gap on the same reconstructed H assigned to job #4;
--   * standard Gaussian Maxwell/Fock reconstruction and same-H restriction.
-- The theorem below manufactures the interacting witness required by the
-- existing Clay-facing OS package. No independent cumulant producer appears.
------------------------------------------------------------------------

round77InteractingWitnessFromWardAndGap :
  ∀ {Observable Point Scalar}
    {system : OS.ContinuumSchwingerSystem Observable Point Scalar} →
  (dataSet : Nontrivial.SameSystemGaussianWardGapData system) →
  OS.InteractingContinuumWitness Observable Point Scalar system
round77InteractingWitnessFromWardAndGap =
  Nontrivial.nonGaussianityGivesInteractingContinuumWitness

round77NontrivialityDependencyCompilerLevel : ProofLevel
round77NontrivialityDependencyCompilerLevel = machineChecked

------------------------------------------------------------------------
-- AUTHORITATIVE ROUND77 CUTSET: FIVE INDEPENDENT PHYSICAL/ANALYTIC JOBS
--
-- 1 CompactSimpleSelectedBackgroundFiveBlockEstimate
--
--   On the literal selected compact-simple background prove
--
--     R_i <= r_i Q, i=1..4,
--     g Q <= G_11,
--     r_1+r_2+r_3+r_4-g <= 55/18874368.
--
--   The signed compiler after these five inequalities is already exact.
--
-- 2 LiteralWilsonFPHaarOneLoopRGCoefficient
--
--   Construct the literal Wilson + reduced FP + Haar Ward-transverse one-loop
--   scalar on the same state, identify its universal 11/24*C_A logarithmic
--   part, and rigorously enclose the four symmetry-reduced regular pieces with
--   enough positive margin to produce the CMP122 small-coupling history.
--
-- 3 PhysicalUnifiedOneStepYMEstimate
--
--   On the ACTUAL source-native CMP119/CMP122 state prove the corrected strong
--   one-step contraction
--
--       || R K - R K' ||_U <= (17/32) || K-K' ||_U
--
--   while carrying composite insertions, separation-weighted connected
--   correlations, the same CMP109 E^(2)/Pi Hessian, characteristic functional,
--   OS data and one common scale-increment modulus. The 1/2+1/32 arithmetic is
--   downstream; the same-norm physical branch estimates are the theorem.
--
-- 4 SameDensityCompactLieHeatLangevinClustering
--
--   On the SAME density/Hessian prove the cutoff/volume-uniform heat/Doob
--   Hessian debt and covariant finite-speed propagation needed for physical
--   exponential clustering. Standard OS transfer then gives a positive gap on
--   the reconstructed Hamiltonian.
--
-- 5 SameFamilyCompositeOPEStressWardClosure
--
--   Prove the nonperturbative composite OPE with quantitative vanishing
--   remainder, local conserved stress tensor with integral T_00 = SAME H, and
--   exact Ward/locality structure on the SAME continuum family.
--
--   ROUND77 STRENGTHENING: under a hypothetical Gaussian limit this same
--   theorem must expose the local O(4)-covariant two-derivative quadratic Ward
--   kernel. The exact classifier then forces Maxwell coefficients. Therefore
--   old job #6 (nontriviality) follows from #4 + #5 + standard Gaussian OS/Fock
--   reconstruction and is no longer independently analytic.
--
-- Trace-class / relative-trace-class / spectral-shift machinery added in this
-- round is an optional quantitative tool inside self-adjoint spectral composite
-- subproblems. It is not counted as another job and is not a generic OPE proof.
------------------------------------------------------------------------

round77IndependentAnalyticCount : Nat
round77IndependentAnalyticCount = 5

------------------------------------------------------------------------
-- NEXT DECREMENT TARGETS
--
-- 5 -> 4 candidate A (most finite): close #1 outright from the existing
-- selected Wilson/KKT/Combes--Thomas/Duhamel machinery by producing the five
-- literal charge-relative constants and checking their signed endpoint.
--
-- 5 -> 4 candidate B: close #2 outright by materializing the literal
-- Wilson/FP/Haar regular DiagramExpression, using exact sign/hyperoctahedral
-- cancellation before intervalization, and enclosing only four representatives.
--
-- Candidate C is structural rather than immediate: if #3's strong composite
-- norm itself gives the full short-distance weighted OPE remainder, the OPE
-- convergence part of #5 becomes downstream, leaving only the local
-- stress/Ward/T00 identification as its endpoint theorem.
------------------------------------------------------------------------
