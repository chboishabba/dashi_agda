module DASHI.ComputerScience.RSA260BidiLeanFiniteFamilyActionBindingExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.ComputerScience.RSA260BidiLeanJointKernelFamilyBindingExact as Joint

------------------------------------------------------------------------
-- LEAN FINITE-FAMILY ACTION LINEARITY DONOR
--
-- The generic Lean branch now has a source-level constructor showing that a
-- finite coefficient family evaluated by per-layer linear actions
--
--   F |-> sum_i L_i (F_i)
--
-- is itself one linear map from the common function module (i -> C) to W.
-- This contracts the earlier RSA binding debt: linearity no longer has to be
-- reproved from scratch once the actual mksol layer actions are exhibited as
-- linear maps L_i.
--
-- It does NOT bind the synthetic runtime harness, exact CADO mksol semantics,
-- a production generator carrier, or the observed zero intersection kernel.
------------------------------------------------------------------------

jointBoundary : Joint.LeanJointKernelFamilyBindingBoundary
jointBoundary = Joint.canonicalLeanJointKernelFamilyBindingBoundary

record LeanFiniteFamilyActionSourceReceipt : Set where
  constructor lean-finite-family-action-source-receipt
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
open LeanFiniteFamilyActionSourceReceipt public

currentLeanFiniteFamilyActionSourceReceipt : LeanFiniteFamilyActionSourceReceipt
currentLeanFiniteFamilyActionSourceReceipt =
  lean-finite-family-action-source-receipt
    "chboishabba/dashi_lean4"
    "agent/rsa-consumer-kernel-bypass"
    "Synthesis/LinearConsumerFiniteFamilyActionRegression.lean"
    "Synthesis/LinearConsumerFiniteFamilyAction.lean"
    "Synthesis.finiteFamilyAction"
    "Synthesis.finiteFamilyAction_apply"
    "9374341154a696f8ee627c34f895432b7306b05a"
    "d258cc67a94fa553f8ecccc3222e94c7b51f8d2c"
    "374f53de680e3356da926744ec14bcc32d30f71a"

------------------------------------------------------------------------
-- WrongType firewalls.
------------------------------------------------------------------------

data GenericFiniteActionCreatesCADOBinding : Set where
data SourceLinearityCreatesJointKernelEquality : Set where
data LeanSourceCreatesKernelReceipt : Set where

genericFiniteActionDoesNotCreateCADOBinding :
  GenericFiniteActionCreatesCADOBinding -> ⊥
genericFiniteActionDoesNotCreateCADOBinding ()

sourceLinearityDoesNotCreateJointKernelEquality :
  SourceLinearityCreatesJointKernelEquality -> ⊥
sourceLinearityDoesNotCreateJointKernelEquality ()

leanSourceDoesNotCreateKernelReceipt : LeanSourceCreatesKernelReceipt -> ⊥
leanSourceDoesNotCreateKernelReceipt ()

record LeanFiniteFamilyActionBindingBoundary : Set where
  constructor lean-finite-family-action-binding-boundary
  field
    leanFiniteFamilyActionSourceWritten : Bool
    genericFiniteLayerSumLinearityWritten : Bool
    commonFunctionModuleConstructorWritten : Bool
    leanKernelReceiptObserved : Bool

    syntheticMksolLayerActionsBoundToDonor : Bool
    syntheticCoefficientCarrierBoundToCommonModule : Bool
    syntheticActionOutputBoundToCommonModule : Bool
    syntheticTwoVFamilyIndexBound : Bool
    formalJointKernelEqualityPaid : Bool

    productionCADOLayerBindingPaid : Bool
    sameObjectProductionCarrierPaid : Bool
    sourceLinearityAloneCreatesProductionInjectivity : Bool
    nextResidual : String
open LeanFiniteFamilyActionBindingBoundary public

canonicalLeanFiniteFamilyActionBindingBoundary :
  LeanFiniteFamilyActionBindingBoundary
canonicalLeanFiniteFamilyActionBindingBoundary =
  lean-finite-family-action-binding-boundary
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
    "kernel-check Synthesis.finiteFamilyAction, then bind the existing synthetic mksol-style coefficient layers to concrete linear maps L_i on one common coefficient module and one common action-output module. After that bind the two-V runtime zero-kernel receipt to the formal jointKernel equality. Production CADO binding and same-object artifacts remain separate."
