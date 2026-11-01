module DASHI.Physics.YangMills.YangMillsContinuumOPEStressWardGaussianKernelExact where

------------------------------------------------------------------------
-- ROUND77: STRENGTHEN THE SAME-FAMILY OPE/STRESS/WARD JOB AT THE RIGHT PLACE
--
-- PRIMARY / CALIBRATION SOURCES
--
-- Arthur Jaffe and Edward Witten,
-- "Quantum Yang-Mills Theory", official Clay Mathematics Institute problem
-- description, in The Millennium Prize Problems. No DOI assigned.
--
-- James Glimm and Arthur Jaffe,
-- "Quantum Physics: A Functional Integral Point of View", 2nd ed., Springer,
-- 1987. DOI: 10.1007/978-1-4612-4728-9.
--
-- Stefan Hollands and Christoph Kopper,
-- "The Operator Product Expansion Converges in Perturbative Field Theory",
-- Communications in Mathematical Physics 313 (2012), 257--290.
-- DOI: 10.1007/s00220-012-1457-4.
--
-- Alexander N. Efremov, Riccardo Guida and Christoph Kopper,
-- "Renormalization of SU(2) Yang-Mills Theory with Flow Equations",
-- Journal of Mathematical Physics 58 (2017), 093503.
-- DOI: 10.1063/1.5000041.
--
-- AUTHORITY BOUNDARY
--
-- The perturbative OPE/flow-equation sources calibrate the local composite
-- architecture only. They do not prove the nonperturbative four-dimensional
-- continuum Yang--Mills theorem below.
--
-- ROUND77 REFACTOR
--
-- The old sixth analytic job was an independent continuum nontriviality
-- estimate. The cheaper route does not need a new fourth-cumulant estimate if
-- the SAME local-field theorem already proves what its Ward/stress content
-- should prove under a hypothetical Gaussian limit:
--
--   Gaussian same-family limit
--     -> local O(4)-covariant two-derivative quadratic kernel
--     -> exact Ward identity on that kernel
--     -> standard Yang--Mills kinetic normalization.
--
-- The coefficient carrier is generic: it need only instantiate the ordinary
-- cancellative additive-group laws, so no rationality premise is imposed on
-- continuum coefficients. The downstream exact classifier gives
-- m^2=0, Z=1, Y=-1. The separate clustering theorem supplies a positive gap on
-- the SAME reconstructed H, so Gaussianity is impossible.
------------------------------------------------------------------------

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanOSMassGapClosure as OS
import DASHI.Physics.YangMills.YangMillsContinuumLocalOperatorOPEStressTensorExact as Local
import DASHI.Physics.YangMills.YangMillsGaussianWardTwoDerivativeMaxwellClassificationExact as Ward

record SameFamilyOPEStressWardGaussianKernel
    (ContinuumFamily CurvaturePolynomial LocalOperator Position
     OPECoefficient StressTensor Hamiltonian Observable Point Scalar : Set)
    (system : OS.ContinuumSchwingerSystem Observable Point Scalar) : Set₂ where
  field
    localPackage :
      Local.ContinuumLocalOperatorOPEStressTensor
        ContinuumFamily CurvaturePolynomial LocalOperator Position
        OPECoefficient StressTensor Hamiltonian

    SameContinuumFamily : ContinuumFamily →
      OS.ContinuumSchwingerSystem Observable Point Scalar → Set
    sameContinuumFamily :
      SameContinuumFamily (Local.continuumFamily localPackage) system

    Gaussian : OS.ContinuumSchwingerSystem Observable Point Scalar → Set

    coefficientAlgebra : Ward.WardCoefficientAdditiveGroup

    -- The physical local theorem supplies the kernel over its actual continuum
    -- scalar algebra. Ward at p^2=1,2 and Z=1 are fields of this SAME object.
    gaussianLocalTwoDerivativeWardKernel :
      Gaussian system →
      Ward.GenericLocalTwoDerivativeWardKernel coefficientAlgebra

open SameFamilyOPEStressWardGaussianKernel public

gaussianKernelClassifiesAsMaxwell :
  ∀ {ContinuumFamily CurvaturePolynomial LocalOperator Position
      OPECoefficient StressTensor Hamiltonian Observable Point Scalar}
    {system : OS.ContinuumSchwingerSystem Observable Point Scalar}
    (dataSet :
      SameFamilyOPEStressWardGaussianKernel
        ContinuumFamily CurvaturePolynomial LocalOperator Position
        OPECoefficient StressTensor Hamiltonian Observable Point Scalar system) →
    (gaussian : Gaussian dataSet system) →
  Ward.GenericMaxwellQuadraticKernelClassification
    (coefficientAlgebra dataSet)
    (gaussianLocalTwoDerivativeWardKernel dataSet gaussian)
gaussianKernelClassifiesAsMaxwell dataSet gaussian =
  Ward.classifyGenericLocalWardKernelAsMaxwell
    (coefficientAlgebra dataSet)
    (gaussianLocalTwoDerivativeWardKernel dataSet gaussian)

sameFamilyGaussianWardMaxwellCompilerLevel : ProofLevel
sameFamilyGaussianWardMaxwellCompilerLevel = machineChecked

physicalSameFamilyOPEStressWardGaussianKernelLevel : ProofLevel
physicalSameFamilyOPEStressWardGaussianKernelLevel = conditional
