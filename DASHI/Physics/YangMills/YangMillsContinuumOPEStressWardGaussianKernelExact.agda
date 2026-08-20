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
-- `YangMillsGaussianWardTwoDerivativeMaxwellClassificationExact` then derives
-- m^2=0, Z=1, Y=-1 by exact rational algebra. The separate clustering theorem
-- supplies a positive gap on the SAME reconstructed H, so Gaussianity is
-- impossible. Thus this local kernel producer belongs inside the existing
-- OPE/stress/Ward job rather than being counted as a seventh/sixth theorem.
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

    -- Exact identification of that package with the SAME continuum Schwinger
    -- family. This blocks splicing a local OPE from one limit with a gap from
    -- another.
    SameContinuumFamily : ContinuumFamily →
      OS.ContinuumSchwingerSystem Observable Point Scalar → Set
    sameContinuumFamily :
      SameContinuumFamily (Local.continuumFamily localPackage) system

    Gaussian : OS.ContinuumSchwingerSystem Observable Point Scalar → Set

    -- This is the strengthened physical content of the Ward/locality endpoint.
    -- The record already contains Ward at p^2=1 and p^2=2 plus Z=1; hence the
    -- downstream Maxwell classification contains no additional analytic input.
    gaussianLocalTwoDerivativeWardKernel :
      Gaussian system → Ward.LocalTwoDerivativeWardKernel

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
  Ward.MaxwellQuadraticKernelClassification
    (gaussianLocalTwoDerivativeWardKernel dataSet gaussian)
gaussianKernelClassifiesAsMaxwell dataSet gaussian =
  Ward.classifyLocalWardKernelAsMaxwell
    (gaussianLocalTwoDerivativeWardKernel dataSet gaussian)

sameFamilyGaussianWardMaxwellCompilerLevel : ProofLevel
sameFamilyGaussianWardMaxwellCompilerLevel = machineChecked

-- This remains one of the five genuine physical jobs: construct the actual
-- nonperturbative OPE/stress/Ward package and, under the Gaussian reductio,
-- derive the local two-derivative Ward kernel from that SAME continuum family.
physicalSameFamilyOPEStressWardGaussianKernelLevel : ProofLevel
physicalSameFamilyOPEStressWardGaussianKernelLevel = conditional
