{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsSameFamilyWardKernelSourceRound563Exact where

------------------------------------------------------------------------
-- GOAL-1 H6 / ROUND563:
-- NARROW SAME-FAMILY WARD SOURCE, WITHOUT FULL OPE/STRESS CARRIER
--
-- The Gaussian nontriviality reductio consumes only:
--
--   * the SAME continuum Schwinger system;
--   * a Gaussian predicate on that system;
--   * the coefficient additive group;
--   * the local two-derivative Ward kernel under Gaussianity.
--
-- It does not consume an OPE coefficient family, OPE remainder, or stress
-- tensor.  Keep those on the conservative Clay local-field finish instead of
-- making them prerequisites of H6.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanOSMassGapClosure as OS
import DASHI.Physics.YangMills.YangMillsGaussianWardTwoDerivativeMaxwellClassificationExact as Ward
import DASHI.Physics.YangMills.YangMillsMinimalWardGapNontrivialityRound549Exact as H6

record SameFamilyWardKernelSource
    {Observable Point Scalar : Set}
    (system : OS.ContinuumSchwingerSystem Observable Point Scalar)
    : Set₁ where
  field
    Gaussian :
      OS.ContinuumSchwingerSystem Observable Point Scalar → Set

    coefficientAlgebra :
      Ward.WardCoefficientAdditiveGroup

    gaussianLocalTwoDerivativeWardKernel :
      Gaussian system →
      Ward.GenericLocalTwoDerivativeWardKernel coefficientAlgebra

open SameFamilyWardKernelSource public

asMinimalSameFamilyGaussianWardKernel :
  ∀ {Observable Point Scalar}
    {system : OS.ContinuumSchwingerSystem Observable Point Scalar} →
  SameFamilyWardKernelSource system →
  H6.MinimalSameFamilyGaussianWardKernel system
asMinimalSameFamilyGaussianWardKernel source = record
  { H6.MinimalSameFamilyGaussianWardKernel.Gaussian =
      Gaussian source
  ; H6.MinimalSameFamilyGaussianWardKernel.coefficientAlgebra =
      coefficientAlgebra source
  ; H6.MinimalSameFamilyGaussianWardKernel.localWardKernelUnderGaussian =
      gaussianLocalTwoDerivativeWardKernel source
  }

round563MinimalWardAdapterLevel : ProofLevel
round563MinimalWardAdapterLevel = machineChecked

round563OPECoefficientRequiredForH6 : Bool
round563OPECoefficientRequiredForH6 = false

round563OPERemainderRequiredForH6 : Bool
round563OPERemainderRequiredForH6 = false

round563StressTensorRequiredForH6 : Bool
round563StressTensorRequiredForH6 = false

-- Genuine physical theorem on the shortest H6 route.
literalRound563SameFamilyWardKernelSourceLevel : ProofLevel
literalRound563SameFamilyWardKernelSourceLevel = conditional
