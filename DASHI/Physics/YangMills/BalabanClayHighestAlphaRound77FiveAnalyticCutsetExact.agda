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
--     -> standard Gaussian OS/Fock gauge-invariant Maxwell composite sector
--        with spectral support accumulating at zero on SAME physical H
--   same-density clustering/gap job (#4)
--     -> positive physical gap on SAME H
--   together -> Gaussian contradiction -> interacting witness.
--
-- Gaussianity alone is NOT being promoted to Maxwell. The genuinely physical
-- local/O(4)/two-derivative Ward-kernel statement is part of job #5. Likewise,
-- the reductio does not use a coloured one-particle state: the no-gap sector is
-- explicitly gauge invariant, as required for the physical Clay Hamiltonian.
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
-- Standard reconstruction/spectral bridge attached to outputs of jobs #4/#5.
--
-- The physical positive gap comes from #4. The physical Gaussian Ward kernel
-- comes from #5. The remaining fields are standard free Gaussian OS/Fock
-- reconstruction into a gauge-invariant curvature-composite continuum and
-- restriction of a SAME-H spectral gap to that invariant physical sector.
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

    gaussianMaxwellPhysicalSector :
      (gaussian : Local.Gaussian localPackage system) →
      Ward.GenericMaxwellQuadraticKernelClassification
        (Local.coefficientAlgebra localPackage)
        (Local.gaussianLocalTwoDerivativeWardKernel localPackage gaussian) →
      Disp.GaplessGaugeInvariantPhysicalSector gapOrder

    PhysicalPositiveGap : OS.Hamiltonian reconstruction → Set
    physicalPositiveGap :
      PhysicalPositiveGap (OS.hamiltonian reconstruction)

    gapRestrictsToSamePhysicalSector :
      (gaussian : Local.Gaussian localPackage system) →
      (classification : Ward.GenericMaxwellQuadraticKernelClassification
        (Local.coefficientAlgebra localPackage)
        (Local.gaussianLocalTwoDerivativeWardKernel localPackage gaussian)) →
      PhysicalPositiveGap (OS.hamiltonian reconstruction) →
      Free.PositiveSpectralGap
        (Disp.gaugeInvariantPhysicalSectorGivesGaplessApproximation
          (gaussianMaxwellPhysicalSector gaussian classification))

    spectralGapContradictionIsAbsurd :
      (gaussian : Local.Gaussian localPackage system) →
      (classification : Ward.GenericMaxwellQuadraticKernelClassification
        (Local.coefficientAlgebra localPackage)
        (Local.gaussianLocalTwoDerivativeWardKernel localPackage gaussian)) →
      let sector = gaussianMaxwellPhysicalSector gaussian classification
          gapData = gapRestrictsToSamePhysicalSector
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
  ; Nontrivial.SameSystemGaussianWardGapData.gaussianMaxwellPhysicalSector =
      gaussianMaxwellPhysicalSector bridge
  ; Nontrivial.SameSystemGaussianWardGapData.PhysicalPositiveGap =
      PhysicalPositiveGap bridge
  ; Nontrivial.SameSystemGaussianWardGapData.physicalPositiveGap =
      physicalPositiveGap bridge
  ; Nontrivial.SameSystemGaussianWardGapData.gapRestrictsToSamePhysicalSector =
      gapRestrictsToSamePhysicalSector bridge
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
--
-- 2 LiteralWilsonFPHaarOneLoopRGCoefficient
--
--   Literal Wilson + reduced FP + Haar Ward-transverse scalar; universal
--   11/24*C_A logarithm plus rigorous four-representative regular enclosure,
--   yielding the CMP122 small-coupling history.
--
-- 3 PhysicalUnifiedOneStepYMEstimate
--
--   On the actual source-native CMP119/CMP122 state prove
--
--       || R K - R K' ||_U <= (17/32) || K-K' ||_U
--
--   in one corrected norm carrying composites, separation-weighted connected
--   correlations, same CMP109 E^(2)/Pi Hessian, characteristic functional, OS
--   data and one common scale-increment modulus.
--
-- 4 SameDensityCompactLieHeatLangevinClustering
--
--   Same-density/Hessian uniform heat/Doob Hessian debt + covariant finite-speed
--   propagation -> physical clustering -> positive gap on reconstructed H.
--
-- 5 SameFamilyCompositeOPEStressWardClosure
--
--   Nonperturbative composite OPE with quantitative vanishing remainder, local
--   conserved stress tensor with integral T_00 = SAME H, and exact
--   Ward/locality structure on SAME continuum family. Under Gaussian reductio,
--   expose the generic local two-derivative Ward kernel; the downstream
--   gauge-invariant Maxwell composite sector and #4 gap force non-Gaussianity.
--
-- The official Jaffe--Witten problem description explicitly asks for local
-- gauge-invariant curvature-polynomial quantum fields and says the required
-- short-distance predictions include a stress tensor and OPE, so #5 is not an
-- optional strengthening on the submission path.
------------------------------------------------------------------------

round77IndependentAnalyticCount : Nat
round77IndependentAnalyticCount = 5

------------------------------------------------------------------------
-- NEXT DECREMENT TARGETS
--
-- 5 -> 4 A: close #1 outright from selected Wilson/KKT/Combes--Thomas/Duhamel
-- machinery by producing the five literal charge-relative constants.
--
-- 5 -> 4 B: close #2 by materializing the literal Wilson/FP/Haar regular
-- DiagramExpression, applying exact sign/hyperoctahedral cancellation before
-- intervalization, then enclosing only four representatives.
--
-- Structural C: if #3's strong composite norm itself gives the full
-- short-distance weighted OPE remainder, OPE convergence in #5 becomes
-- downstream and only local stress/Ward/T00 identification remains.
------------------------------------------------------------------------
