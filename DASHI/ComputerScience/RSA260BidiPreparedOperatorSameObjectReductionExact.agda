module DASHI.ComputerScience.RSA260BidiPreparedOperatorSameObjectReductionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.ComputerScience.RSA260BidiRuntimeKrylovActionBindingExact as Runtime
import DASHI.ComputerScience.RSA260BidiLeanKrylovFamilyActionBindingExact as Lean

------------------------------------------------------------------------
-- PREPARED-OPERATOR SAME-OBJECT REDUCTION
--
-- The committed synthetic runtime baseline uses the identity middle
-- permutation, hence
--
--   apply_B Y = A ((A^T) Y).
--
-- The new domain-neutral Lean donor defines the formal prepared operator by
-- left multiplication with A A^T and proves, by matrix associativity,
--
--   (A A^T) Y = A (A^T Y).
--
-- Therefore the remaining runtime/formal operator payment is no longer an
-- opaque function-equality problem.  In this exact baseline context it reduces
-- to the same-object identification of the rectangular runtime matrix A with
-- the formal Lean matrix A.  That identity is NOT paid here.
------------------------------------------------------------------------

runtimeBoundary : Runtime.RuntimeKrylovActionBindingBoundary
runtimeBoundary = Runtime.canonicalRuntimeKrylovActionBindingBoundary

leanBoundary : Lean.LeanKrylovFamilyActionBindingBoundary
leanBoundary = Lean.canonicalLeanKrylovFamilyActionBindingBoundary

record LeanPreparedOperatorSourceReceipt : Set where
  constructor lean-prepared-operator-source-receipt
  field
    repository : String
    branch : String
    regressionPath : String
    sourcePath : String
    constructorName : String
    applicationTheoremName : String
    redCommit : String
    sourceCommit : String
    rootIntegrationCommit : String
open LeanPreparedOperatorSourceReceipt public

currentLeanPreparedOperatorSourceReceipt : LeanPreparedOperatorSourceReceipt
currentLeanPreparedOperatorSourceReceipt =
  lean-prepared-operator-source-receipt
    "chboishabba/dashi_lean4"
    "agent/rsa-consumer-kernel-bypass"
    "Synthesis/LinearConsumerPreparedOperatorRegression.lean"
    "Synthesis/LinearConsumerPreparedOperator.lean"
    "Synthesis.gramPreparedOperator"
    "Synthesis.gramPreparedOperator_apply"
    "e0665b612dba42f33bbc52f0e6fd7f4656a5893f"
    "79e01009452e894aa78d903819fbf5a7471a62c6"
    "cea0bb9d2caaa8a2821ff37c04939302ff38edc1"

------------------------------------------------------------------------
-- Proof-debt types.
--
-- `MatrixASameObjectPayment` is intentionally uninhabited here.  A prepared
-- operator binding can only be constructed from that exact payment.  This
-- records the contraction of the residual without laundering the runtime hash
-- into a formal equality proof.
------------------------------------------------------------------------

data MatrixASameObjectPayment : Set where

data PreparedOperatorBindingPayment : Set where
  prepared-operator-binding :
    MatrixASameObjectPayment -> PreparedOperatorBindingPayment

preparedOperatorBindingRequiresMatrixA :
  PreparedOperatorBindingPayment -> MatrixASameObjectPayment
preparedOperatorBindingRequiresMatrixA (prepared-operator-binding sameA) = sameA

matrixASameObjectStillUnpaid : MatrixASameObjectPayment -> ⊥
matrixASameObjectStillUnpaid ()

------------------------------------------------------------------------
-- Exact current boundary.
------------------------------------------------------------------------

record PreparedOperatorSameObjectBoundary : Set where
  constructor prepared-operator-same-object-boundary
  field
    runtimeProducerCommitted : Bool
    runtimeIdentityPermutationPaid : Bool
    runtimeMatrixADigestRetained : Bool
    runtimeApplyBFormulaPaid : Bool
    leanPreparedOperatorSourceWritten : Bool
    leanAssociativityBridgeSourceWritten : Bool

    leanKernelReceiptObserved : Bool
    runtimeMatrixABoundToLeanMatrixA : Bool
    runtimeApplyBBoundToLeanPreparedOperator : Bool
    runtimeSeedVBoundToLeanV : Bool
    runtimeRecoveredFBoundToLeanF : Bool
    runtimeActionBoundToLeanKrylovAction : Bool
    twoVRuntimeKernelBoundToFormalJointKernel : Bool

    exactCADOMksolSemanticsPaid : Bool
    productionSameObjectCarrierPaid : Bool
open PreparedOperatorSameObjectBoundary public

canonicalPreparedOperatorSameObjectBoundary : PreparedOperatorSameObjectBoundary
canonicalPreparedOperatorSameObjectBoundary =
  prepared-operator-same-object-boundary
    true true true true true true
    false false false false false false false
    false false

data PreparedOperatorSameObjectResidual : Set where
  bindRuntimeMatrixAToLeanMatrixA : PreparedOperatorSameObjectResidual
  bindRuntimeSeedVToLeanV : PreparedOperatorSameObjectResidual
  bindRuntimeRecoveredFToLeanF : PreparedOperatorSameObjectResidual
  bindRuntimeActionToLeanKrylovAction : PreparedOperatorSameObjectResidual
  transportTwoVKernelToFormalJointKernel : PreparedOperatorSameObjectResidual
  bindExactCADOMksolSemantics : PreparedOperatorSameObjectResidual
  bindProductionSameObjectCarrier : PreparedOperatorSameObjectResidual

firstPreparedOperatorSameObjectResidual : PreparedOperatorSameObjectResidual
firstPreparedOperatorSameObjectResidual = bindRuntimeMatrixAToLeanMatrixA
