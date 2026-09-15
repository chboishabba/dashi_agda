module DASHI.ComputerScience.RSA260BidiLeanMatrixFamilyActionBindingExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.ComputerScience.RSA260BidiLeanFiniteFamilyActionBindingExact as Family

------------------------------------------------------------------------
-- LEAN MATRIX-FAMILY ACTION DONOR
--
-- Pinned mathlib already provides Matrix.mulLeftLinearMap: for fixed K,
--
--   F |-> K * F
--
-- is a linear map in F.  The RSA Lean branch now composes this with the
-- previously-written finiteFamilyAction donor to obtain
--
--   F |-> sum_i K_i * F_i
--
-- as one linear map on the common finite coefficient-family module.
--
-- This pays the generic matrix-linearity/assembly layer only.  It does not
-- identify the formal K_i with the synthetic runtime Krylov blocks M^i V,
-- does not bind an exact CADO prepared operator/V/range family, and does not
-- convert a runtime matrix-rank calculation into the formal jointKernel = bot
-- proposition expected by the generic Lean joint-kernel theorem.
------------------------------------------------------------------------

familyBoundary : Family.LeanFiniteFamilyActionBindingBoundary
familyBoundary = Family.canonicalLeanFiniteFamilyActionBindingBoundary

record LeanMatrixFamilyActionSourceReceipt : Set where
  constructor lean-matrix-family-action-source-receipt
  field
    repository : String
    branch : String
    regressionPath : String
    sourcePath : String
    layerConstructorName : String
    familyConstructorName : String
    familyApplicationTheoremName : String
    redCommit : String
    sourceCommit : String
    rootIntegrationCommit : String
    pinnedMathlibDonor : String
open LeanMatrixFamilyActionSourceReceipt public

currentLeanMatrixFamilyActionSourceReceipt : LeanMatrixFamilyActionSourceReceipt
currentLeanMatrixFamilyActionSourceReceipt =
  lean-matrix-family-action-source-receipt
    "chboishabba/dashi_lean4"
    "agent/rsa-consumer-kernel-bypass"
    "Synthesis/LinearConsumerMatrixFamilyActionRegression.lean"
    "Synthesis/LinearConsumerMatrixFamilyAction.lean"
    "Synthesis.matrixLayerAction"
    "Synthesis.matrixCoefficientFamilyAction"
    "Synthesis.matrixCoefficientFamilyAction_apply"
    "aa02aed854b1a8b5c64a6d0619f2fec93770a65c"
    "18b00239614eb72026815e8fefdfa5a52832fd57"
    "612d4e25f46c3bde5b41832c6f03891409d5acce"
    "Mathlib.LinearAlgebra.Matrix.Bilinear / Matrix.mulLeftLinearMap @ mathlib v4.28.0"

------------------------------------------------------------------------
-- WrongType firewalls.
------------------------------------------------------------------------

data GenericMatrixActionCreatesKrylovIdentity : Set where
data SourceMatrixLinearityCreatesJointKernelReceipt : Set where
data LeanMatrixSourceCreatesProductionBinding : Set where

genericMatrixActionDoesNotCreateKrylovIdentity :
  GenericMatrixActionCreatesKrylovIdentity -> ⊥
genericMatrixActionDoesNotCreateKrylovIdentity ()

sourceMatrixLinearityDoesNotCreateJointKernelReceipt :
  SourceMatrixLinearityCreatesJointKernelReceipt -> ⊥
sourceMatrixLinearityDoesNotCreateJointKernelReceipt ()

leanMatrixSourceDoesNotCreateProductionBinding :
  LeanMatrixSourceCreatesProductionBinding -> ⊥
leanMatrixSourceDoesNotCreateProductionBinding ()

record LeanMatrixFamilyActionBindingBoundary : Set where
  constructor lean-matrix-family-action-binding-boundary
  field
    leanMatrixFamilyActionSourceWritten : Bool
    pinnedMathlibMulLeftLinearMapLocated : Bool
    fixedLeftMatrixLayerLinearityWritten : Bool
    matrixCoefficientFamilyActionWritten : Bool
    commonGF2MatrixModuleSurfaceWritten : Bool
    leanKernelReceiptObserved : Bool

    syntheticKrylovLayerMatricesBound : Bool
    syntheticGeneratorCoefficientMatricesBound : Bool
    syntheticActionEqualityToRuntimeHarnessPaid : Bool
    syntheticTwoVFamilyIndexBound : Bool
    formalJointKernelEqualityPaid : Bool

    productionCADOKrylovLayerBindingPaid : Bool
    productionPreparedOperatorBindingPaid : Bool
    productionVBindingPaid : Bool
    productionRangeBindingPaid : Bool
    sourceLinearityCreatesProductionAdequacy : Bool
    nextResidual : String
open LeanMatrixFamilyActionBindingBoundary public

canonicalLeanMatrixFamilyActionBindingBoundary :
  LeanMatrixFamilyActionBindingBoundary
canonicalLeanMatrixFamilyActionBindingBoundary =
  lean-matrix-family-action-binding-boundary
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
    false
    "bind the existing synthetic Krylov blocks K_i = M^i V and recovered coefficient matrices F_i to Synthesis.matrixCoefficientFamilyAction, then prove equality with the runtime mksol-style action before interpreting the two-V zero-kernel receipt as a formal jointKernel statement. Production CADO K_i / prepared-operator / V / range binding remains separate."
