module DASHI.Physics.YangMills.BalabanClayHighestAlphaRound77FiveAnalyticCutsetExact where

------------------------------------------------------------------------
-- ROUND77: 6 -> 5 INDEPENDENT ANALYTIC JOBS
--
-- Round76 left `InteractingContinuumNontriviality` as a separate sixth job.
-- The structural Gaussian reductio is now opened far enough that no independent
-- fourth-cumulant estimate is needed on the shortest route.
--
--   strengthened same-family OPE/stress/Ward job (#5)
--     -> hypothetical Gaussian local two-derivative Ward kernel
--     -> exact generic coefficient algebra: m^2=0, Z=1, Y=-1
--     -> standard Gaussian OS/Fock Maxwell sector on SAME H
--   same-density clustering/gap job (#4)
--     -> positive physical gap on SAME H
--   together -> Gaussian contradiction -> interacting witness.
--
-- Gaussianity alone is NOT being promoted to Maxwell. The genuinely physical
-- local/O(4)/two-derivative Ward-kernel statement is part of job #5.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanOSMassGapClosure as OS
import DASHI.Physics.YangMills.BalabanClayHighestAlphaRound76SixAnalyticCutsetExact
import DASHI.Physics.YangMills.YangMillsFreeGaussianMaxwellNoGapExact as Free
import DASHI.Physics.YangMills.YangMillsMaxwellLinearDispersionNoGapExact as Disp
import DASHI.Physics.YangMills.YangMillsContinuumOPEStressWardGaussianKernelExact as Local
import DASHI.Physics.YangMills.YangMillsGaussianWardTwoDerivativeMaxwellClassificationExact as Ward
import DASHI.Physics.YangMills.YangMillsGaussianWardGapNontrivialityExact as Nontrivial
import DASHI.Physics.YangMills.SchattenTraceClassCompositePerturbationExact

------------------------------------------------------------------------
-- Standard reconstruction/spectral bridge attached to the output of jobs #4/#5.
--
-- No new physical estimate lives here. `localPackage` already owns the Ward
-- kernel under the Gaussian reductio; `physicalPositiveGap` is the output of
-- the clustering theorem. The remaining fields are the standard free Gaussian
-- OS/Fock identification and restriction of a SAME-H spectral gap to a
-- one-particle invariant sector.
------------------------------------------------------------------------

record StandardGaussianMaxwellSameHGapBridge
    {ContinuumFamily CurvaturePolynomial LocalOperator Position
     OPECoefficient StressTensor Hamiltonian Observable Point Scalar : Set}
    {system : OS.ContinuumSchwingerSystem Observable Point Scalar}
    (localPackage :
      Local.SameFamilyOPEStressWardGaussianKernel
        ContinuumFamily CurvaturePolynomial LocalOperator Position
        OPECoefficient StressTensor Hamiltonian Observable Point Scalar system)
    : Set₂ where
  field
    reconstruction : OS.OSReconstructionAuthority Observable Point Scalar system
    gapOrder : Free.GapOrder

    gaussianMaxwellDispersion :
      (gaussian : Local.Gaussian localPackage system) →
      Ward.GenericMaxwellQuadraticKernelClassification
        (Local.coefficientAlgebra localPackage)
        (Local.gaussianLocalTwoDerivativeWardKernel localPackage gaussian) →
      Disp.LabelledLinearMasslessDispersion gapOrder

    PhysicalPositiveGap : OS.Hamiltonian reconstruction → Set
    physicalPositiveGap :
      PhysicalPositiveGap (OS.hamiltonian reconstruction)

    gapRestrictsToSameMaxwellSector :
      (gaussian : Local.Gaussian localPackage system) →
      (classification : Ward.GenericMaxwellQuadraticKernelClassification
        (Local.coefficientAlgebra localPackage)
        (Local.gaussianLocalTwoDerivativeWardKernel localPackage gaussian)) →
      PhysicalPositiveGap (OS.hamiltonian reconstruction) →
      Free.PositiveSpectralGap
        (Disp.labelledLinearDispersionGivesMasslessSector
          (gaussianMaxwellDispersion gaussian classification))

    spectralGapContradictionIsAbsurd :
      (gaussian : Local.Gaussian localPackage system) →
      (classification : Ward.GenericMaxwellQuadraticKernelClassification
        (Local.coefficientAlgebra localPackage)
        (Local.gaussianLocalTwoDerivativeWardKernel localPackage gaussian)) →
      let dispersion = gaussianMaxwellDispersion gaussian classification
          gapData = gapRestrictsToSameMaxwellSector
            gaussian classification physicalPositiveGap
      in
      Free.SpectralContradiction gapData → ⊥

open StandardGaussianMaxwellSameHGapBridge public

sameFamilyLocalAndGapData :
  ∀ {ContinuumFamily CurvaturePolynomial LocalOperator Position
      OPECoefficient StressTensor Hamiltonian Observable Point Scalar}
    {system : OS.ContinuumSchwingerSystem Observable Point Scalar}
    (localPackage :
      Local.SameFamilyOPEStressWardGaussianKernel
        ContinuumFamily CurvaturePolynomial LocalOperator Position
        OPECoefficient StressTensor Hamiltonian Observable Point Scalar system) →
    (bridge : StandardGaussianMaxwellSameHGapBridge localPackage) →
  Nontrivial.SameSystemGaussianWardGapData system
sameFamilyLocalAndGapData localPackage bridge = record
  { Nontrivial.SameSystemGaussianWardGapData.reconstruction = reconstruction bridge
  ; Nontrivial.SameSystemGaussianWardGapData.Gaussian = Local.Gaussian localPackage
  ; Nontrivial.SameSystemGaussianWardGapData.coefficientAlgebra =
      Local.coefficientAlgebra localPackage
  ; Nontrivial.SameSystemGaussianWardGapData.localWardKernelUnderGaussian =
      Local.gaussianLocalTwoDerivativeWardKernel localPackage
  ; Nontrivial.SameSystemGaussianWardGapData.gapOrder = gapOrder bridge
  ; Nontrivial.SameSystemGaussianWardGapData.gaussianMaxwellDispersion =
      gaussianMaxwellDispersion bridge
  ; Nontrivial.SameSystemGaussianWardGapData.PhysicalPositiveGap =
      PhysicalPositiveGap bridge
  ; Nontrivial.SameSystemGaussianWardGapData.physicalPositiveGap =
      physicalPositiveGap bridge
  ; Nontrivial.SameSystemGaussianWardGapData.gapRestrictsToSameMaxwellSector =
      gapRestrictsToSameMaxwellSector bridge
  ; Nontrivial.SameSystemGaussianWardGapData.spectralGapContradictionIsAbsurd =
      spectralGapContradictionIsAbsurd bridge
  }

round77InteractingWitnessFromLocalAndGap :
  ∀ {ContinuumFamily CurvaturePolynomial LocalOperator Position
      OPECoefficient StressTensor Hamiltonian Observable Point Scalar}
    {system : OS.ContinuumSchwingerSystem Observable Point Scalar}
    (localPackage :
      Local.SameFamilyOPEStressWardGaussianKernel
        ContinuumFamily CurvaturePolynomial LocalOperator Position
        OPECoefficient StressTensor Hamiltonian Observable Point Scalar system) →
    (bridge : StandardGaussianMaxwellSameHGapBridge localPackage) →
  OS.InteractingContinuumWitness Observable Point Scalar system
round77InteractingWitnessFromLocalAndGap localPackage bridge =
  Nontrivial.nonGaussianityGivesInteractingContinuumWitness
    (sameFamilyLocalAndGapData localPackage bridge)

round77NontrivialityDependencyCompilerLevel : ProofLevel
round77NontrivialityDependencyCompilerLevel = machineChecked

standardGaussianMaxwellSameHGapBridgeLevel : ProofLevel
standardGaussianMaxwellSameHGapBridgeLevel = standardImported

------------------------------------------------------------------------
-- AUTHORITATIVE ROUND77 CUTSET: FIVE INDEPENDENT PHYSICAL/ANALYTIC JOBS
--
-- 1 CompactSimpleSelectedBackgroundFiveBlockEstimate
--
--   R_i <= r_i Q, i=1..4,
--   g Q <= G_11,
--   r_1+r_2+r_3+r_4-g <= 55/18874368.
--   The signed compiler after these inequalities is exact.
--
-- 2 LiteralWilsonFPHaarOneLoopRGCoefficient
--
--   Construct the literal Wilson + reduced FP + Haar Ward-transverse scalar,
--   identify the universal 11/24*C_A logarithmic part and rigorously enclose
--   the four symmetry-reduced regular pieces with enough positive margin to
--   produce the CMP122 small-coupling history.
--
-- 3 PhysicalUnifiedOneStepYMEstimate
--
--   On the ACTUAL source-native CMP119/CMP122 state prove
--
--       || R K - R K' ||_U <= (17/32) || K-K' ||_U
--
--   in one corrected strong norm carrying composite insertions,
--   separation-weighted connected correlations, the same CMP109 E^(2)/Pi
--   Hessian, characteristic functional, OS data and one common scale-increment
--   modulus. The 1/2+1/32 arithmetic is already downstream.
--
-- 4 SameDensityCompactLieHeatLangevinClustering
--
--   On the SAME density/Hessian prove the cutoff/volume-uniform heat/Doob
--   Hessian debt and covariant finite-speed propagation needed for physical
--   exponential clustering. Standard OS transfer gives the positive gap on H.
--
-- 5 SameFamilyCompositeOPEStressWardClosure
--
--   Prove the nonperturbative composite OPE with quantitative vanishing
--   remainder, local conserved stress tensor with integral T_00 = SAME H, and
--   exact Ward/locality structure on the SAME continuum family.
--
--   Round77 strengthening: under a hypothetical Gaussian limit this theorem
--   also exposes the local O(4)-covariant two-derivative quadratic Ward kernel
--   over the actual continuum scalar algebra. The exact generic classifier
--   forces Maxwell coefficients; #4 then contradicts the massless sector.
--
-- Trace-class / relative-trace-class / spectral-shift machinery is an optional
-- quantitative tool inside self-adjoint spectral-composite subproblems. It is
-- not counted as another job and is not a generic OPE proof.
------------------------------------------------------------------------

round77IndependentAnalyticCount : Nat
round77IndependentAnalyticCount = 5

------------------------------------------------------------------------
-- NEXT DECREMENT TARGETS
--
-- 5 -> 4 A: close #1 outright using selected Wilson/KKT/Combes--Thomas/Duhamel
-- machinery to produce the five literal charge-relative constants.
--
-- 5 -> 4 B: close #2 by materializing the literal Wilson/FP/Haar regular
-- DiagramExpression, applying exact sign/hyperoctahedral cancellation before
-- intervalization, then enclosing only four representatives.
--
-- Structural C: if #3's strong composite norm itself gives the full
-- short-distance weighted OPE remainder, OPE convergence in #5 becomes
-- downstream and only local stress/Ward/T00 identification remains.
------------------------------------------------------------------------
