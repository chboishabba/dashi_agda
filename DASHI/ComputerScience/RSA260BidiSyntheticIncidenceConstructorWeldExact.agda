module DASHI.ComputerScience.RSA260BidiSyntheticIncidenceConstructorWeldExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.ComputerScience.RSA260BidiPreparedOperatorSameObjectReductionExact as Prepared

------------------------------------------------------------------------
-- SYNTHETIC INCIDENCE CONSTRUCTOR WELD
--
-- The runtime matrix A is now exposed by two independently inspectable finite
-- constructors rather than only by a digest.
--
-- dashiRTX original constructor:
--   degree(r) = 151 for r < 6, else 150
--   base(r)   = (2654435761*r + 0x9e3779b9) mod 512
--   support   = base(r) + {0,...,degree(r)-1} mod 512.
--
-- dashiRTX extensional constructor and Lean source use the equivalent entrywise
-- formula
--
--   A[r,c] = 1 iff ((c + 512 - base(r)) mod 512) < degree(r).
--
-- A local exhaustive runtime check compared all 924*512 finite entries between
-- the original and extensional Python constructors and observed zero mismatches.
-- Lean now source-defines that same arithmetic formula over Fin 924 x Fin 512.
--
-- This does NOT yet promote the runtime equality check into a Lean kernel proof
-- or a cross-prover same-object theorem.  It contracts the residual from an
-- opaque matrix-hash identity to transport of one explicit finite constructor.
------------------------------------------------------------------------

preparedBoundary : Prepared.PreparedOperatorSameObjectBoundary
preparedBoundary = Prepared.canonicalPreparedOperatorSameObjectBoundary

record RuntimeExtensionalIncidenceReceipt : Set where
  constructor runtime-extensional-incidence-receipt
  field
    repository : String
    branch : String
    regressionPath : String
    producerPath : String
    redCommit : String
    greenCommit : String
    producerGitBlob : String
    rows : Nat
    cols : Nat
    checkedEntryCount : Nat
    mismatchCount : Nat
    runtimeOriginalEqualsExtensional : Bool
    runtimeAOriginalSHA256 : String
    runtimeAExtensionalSHA256 : String
    exactFiniteCheckExecuted : Bool
open RuntimeExtensionalIncidenceReceipt public

currentRuntimeExtensionalIncidenceReceipt : RuntimeExtensionalIncidenceReceipt
currentRuntimeExtensionalIncidenceReceipt =
  runtime-extensional-incidence-receipt
    "chboishabba/dashiRTX"
    "agent/triadic-u8-runtime-oracle"
    "test_rsa260_bidi_mksol_action_binding.py"
    "rsa260_bidi_mksol_action_binding.py"
    "6af63cd76fc150172566932f54890d42a2d84fa4"
    "672e9627711b306ffe9209b21f680fbb22132fa6"
    "f8efaca307973966142f339c3b000ec2786cbe31"
    924 512 473088 0 true
    "d25f6dc6148fef994b803bf763835e6ceda13cd1fdb7ed62faa5f34e64a2b09d"
    "d25f6dc6148fef994b803bf763835e6ceda13cd1fdb7ed62faa5f34e64a2b09d"
    true

record LeanSyntheticIncidenceSourceReceipt : Set where
  constructor lean-synthetic-incidence-source-receipt
  field
    repository : String
    branch : String
    regressionPath : String
    sourcePath : String
    rowDegreeName : String
    rowBaseName : String
    incidenceName : String
    preparedOperatorName : String
    redCommit : String
    sourceCommit : String
    rootIntegrationCommit : String
open LeanSyntheticIncidenceSourceReceipt public

currentLeanSyntheticIncidenceSourceReceipt : LeanSyntheticIncidenceSourceReceipt
currentLeanSyntheticIncidenceSourceReceipt =
  lean-synthetic-incidence-source-receipt
    "chboishabba/dashi_lean4"
    "agent/rsa-consumer-kernel-bypass"
    "Synthesis/LinearConsumerSyntheticBidiIncidenceRegression.lean"
    "Synthesis/LinearConsumerSyntheticBidiIncidence.lean"
    "Synthesis.syntheticBidiRowDegree"
    "Synthesis.syntheticBidiRowBase"
    "Synthesis.syntheticBidiIncidence"
    "Synthesis.syntheticBidiPreparedOperator"
    "87e2b28d14fac02f70d5d13c0f5d144c702a80be"
    "42e9e2832d9e1d6379b94f2a228072da653c0c38"
    "692c4199fa0862bca6d056295ae83782539b31e9"

------------------------------------------------------------------------
-- Cross-language payment stays proof relevant and unpaid.
------------------------------------------------------------------------

data RuntimeConstructorEqualsLeanConstructor : Set where

data RuntimePreparedOperatorEqualsLeanPreparedOperator : Set where
  runtime-prepared-operator-equals-lean :
    RuntimeConstructorEqualsLeanConstructor ->
    RuntimePreparedOperatorEqualsLeanPreparedOperator

constructorIdentityStillUnpaid : RuntimeConstructorEqualsLeanConstructor -> ⊥
constructorIdentityStillUnpaid ()

preparedIdentityRequiresConstructorIdentity :
  RuntimePreparedOperatorEqualsLeanPreparedOperator ->
  RuntimeConstructorEqualsLeanConstructor
preparedIdentityRequiresConstructorIdentity
  (runtime-prepared-operator-equals-lean witness) = witness

record SyntheticIncidenceConstructorWeldBoundary : Set where
  constructor synthetic-incidence-constructor-weld-boundary
  field
    runtimeOriginalConstructorCommitted : Bool
    runtimeExtensionalConstructorCommitted : Bool
    runtimeExtensionalConstructorMatchesOriginal : Bool
    runtimeAllEntriesChecked : Bool
    runtimeConstructorDigestAgreementObserved : Bool
    leanExactFiniteConstructorSourceWritten : Bool
    leanPreparedOperatorFromExactConstructorSourceWritten : Bool

    leanKernelReceiptObserved : Bool
    runtimeConstructorBoundToLeanConstructor : Bool
    runtimePreparedOperatorBoundToLeanPreparedOperator : Bool
    runtimeSeedVBoundToLeanV : Bool
    runtimeRecoveredFBoundToLeanF : Bool
    runtimeActionBoundToLeanKrylovAction : Bool
    twoVRuntimeKernelBoundToFormalJointKernel : Bool

    exactCADOMksolSemanticsPaid : Bool
    productionSameObjectCarrierPaid : Bool
open SyntheticIncidenceConstructorWeldBoundary public

canonicalSyntheticIncidenceConstructorWeldBoundary :
  SyntheticIncidenceConstructorWeldBoundary
canonicalSyntheticIncidenceConstructorWeldBoundary =
  synthetic-incidence-constructor-weld-boundary
    true true true true true true true
    false false false false false false false
    false false

data SyntheticIncidenceConstructorResidual : Set where
  transportExplicitFiniteConstructorIntoLean : SyntheticIncidenceConstructorResidual
  bindRuntimeSeedVToLeanV : SyntheticIncidenceConstructorResidual
  bindRuntimeRecoveredFToLeanF : SyntheticIncidenceConstructorResidual
  bindRuntimeActionToLeanKrylovAction : SyntheticIncidenceConstructorResidual
  transportTwoVKernelToFormalJointKernel : SyntheticIncidenceConstructorResidual
  bindExactCADOMksolSemantics : SyntheticIncidenceConstructorResidual
  bindProductionSameObjectCarrier : SyntheticIncidenceConstructorResidual

firstSyntheticIncidenceConstructorResidual : SyntheticIncidenceConstructorResidual
firstSyntheticIncidenceConstructorResidual = transportExplicitFiniteConstructorIntoLean
