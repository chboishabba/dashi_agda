module DASHI.ComputerScience.RSA260BidiLeanKrylovFamilyActionBindingExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.ComputerScience.RSA260BidiLeanMatrixFamilyActionBindingExact as MatrixBinding

------------------------------------------------------------------------
-- LEAN KRYLOV-FAMILY ACTION BINDING
--
-- The Lean bypass now has a domain-neutral specialization of the rectangular
-- matrix-family action to the exact recurrence shape
--
--   K_i = M^i V
--   action(F) = sum_i (M^i V) F_i.
--
-- This removes the generic Krylov/action algebra from the RSA proof debt.
-- The remaining payments are same-object identifications:
--   * runtime apply_B / prepared operator with the formal linear endomorphism M;
--   * seeded runtime V with the formal seed block V;
--   * recovered generator coefficient layers with the formal F_i family;
--   * the runtime action digest/rank matrix with the resulting formal linear map.
--
-- No runtime or production identity is promoted here.
------------------------------------------------------------------------

matrixBoundary : MatrixBinding.LeanMatrixFamilyActionBindingBoundary
matrixBoundary = MatrixBinding.canonicalLeanMatrixFamilyActionBindingBoundary

record LeanKrylovFamilyActionSourceReceipt : Set where
  constructor lean-krylov-family-action-source-receipt
  field
    repository : String
    branch : String
    regressionPath : String
    sourcePath : String
    constructorName : String
    applicationTheoremName : String
    rectangularRegressionCommit : String
    rectangularSourceCommit : String
    redCommit : String
    sourceCommit : String
    rootIntegrationCommit : String
open LeanKrylovFamilyActionSourceReceipt public

currentLeanKrylovFamilyActionSourceReceipt : LeanKrylovFamilyActionSourceReceipt
currentLeanKrylovFamilyActionSourceReceipt =
  lean-krylov-family-action-source-receipt
    "chboishabba/dashi_lean4"
    "agent/rsa-consumer-kernel-bypass"
    "Synthesis/LinearConsumerKrylovFamilyActionRegression.lean"
    "Synthesis/LinearConsumerKrylovFamilyAction.lean"
    "Synthesis.krylovCoefficientFamilyAction"
    "Synthesis.krylovCoefficientFamilyAction_apply"
    "fe202d0f6e77d80f1dcf67e8b890ad75fd2fd3df"
    "de8b13c5f8510e6bb8bc49810cf9fd0f3e053cfb"
    "c2090cb3683eb36f8611eb318f454caa04a52efa"
    "7c513b4ceda078ea5311432bf70fc429f091b4f3"
    "c47568ff01fd4eb2e1965f11d41c2dbbf3f4fa47"

------------------------------------------------------------------------
-- WrongType firewalls.
------------------------------------------------------------------------

data LeanKrylovSourceCreatesRuntimeBinding : Set where
data RuntimeShapeCreatesProductionSameObject : Set where
data RuntimeZeroKernelCreatesFormalJointKernel : Set where

leanKrylovSourceDoesNotCreateRuntimeBinding :
  LeanKrylovSourceCreatesRuntimeBinding -> ⊥
leanKrylovSourceDoesNotCreateRuntimeBinding ()

runtimeShapeDoesNotCreateProductionSameObject :
  RuntimeShapeCreatesProductionSameObject -> ⊥
runtimeShapeDoesNotCreateProductionSameObject ()

runtimeZeroKernelDoesNotCreateFormalJointKernel :
  RuntimeZeroKernelCreatesFormalJointKernel -> ⊥
runtimeZeroKernelDoesNotCreateFormalJointKernel ()

record LeanKrylovFamilyActionBindingBoundary : Set where
  constructor lean-krylov-family-action-binding-boundary
  field
    rectangularCarrierBugDetected : Bool
    rectangularRegressionWritten : Bool
    rectangularMatrixFamilySourceWritten : Bool
    genericKrylovFamilyActionSourceWritten : Bool
    genericFormulaIsSumMiVFi : Bool
    leanKernelReceiptObserved : Bool

    runtimeApplyBBoundToFormalM : Bool
    runtimeSeedBlockBoundToFormalV : Bool
    runtimeRecoveredCoefficientsBoundToFormalFamily : Bool
    runtimeActionBoundToFormalKrylovFamilyAction : Bool
    twoVRuntimeKernelBoundToFormalJointKernel : Bool

    productionPreparedOperatorSameObjectPaid : Bool
    productionVBlocksSameObjectPaid : Bool
    productionGeneratorSameObjectPaid : Bool
    productionCADOMksolSemanticsPaid : Bool

    nextResidual : String
open LeanKrylovFamilyActionBindingBoundary public

canonicalLeanKrylovFamilyActionBindingBoundary :
  LeanKrylovFamilyActionBindingBoundary
canonicalLeanKrylovFamilyActionBindingBoundary =
  lean-krylov-family-action-binding-boundary
    true
    true
    true
    true
    true
    false
    false
    false
    false
    false
    false
    false
    false
    false
    false
    "kernel-check the Lean rectangular/Krylov donors, then bind the synthetic runtime apply_B operator to the formal linear endomorphism M, the seeded runtime V block to formal V, and the recovered coefficient layers to formal F_i. Only then identify the runtime sum_i M^i V F_i with Synthesis.krylovCoefficientFamilyAction and transport the two-V zero-kernel receipt into the formal jointKernel theorem. Production CADO same-object bindings remain separate."
