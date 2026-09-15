module DASHI.ComputerScience.RSA260BidiLeanJointKernelFamilyBindingExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.ComputerScience.RSA260BidiLeanConsumerKernelBypassExact as Lean
import DASHI.ComputerScience.RSA260BidiMksolVContextStressExact as Stress
import DASHI.ComputerScience.RSA260BidiCADOMksolContextFamilyExact as CADOFamily

------------------------------------------------------------------------
-- DECLARED-FAMILY BINDING FOR THE GENERIC LEAN JOINT-KERNEL DONOR
--
-- The Lean donor is a theorem about a family of *linear maps* on one common
-- module.  The RSA/CADO Agda owners currently expose generic evaluator
-- interfaces and runtime rank receipts.  Therefore a zero intersection-kernel
-- runtime observation does not by itself instantiate the Lean theorem.
--
-- Required weld:
--   generator coefficient carrier -> one Lean module V
--   each declared (V, prepared-operator, solution-range) context -> A_i
--   A_i : V ->_R W as an actual linear map
--   runtime/formal joint-kernel receipt -> jointKernel A = bottom
--
-- Only after those payments and Lean kernel certification may the generic
-- theorem replace hand-recorded joint-injectivity bookkeeping.
------------------------------------------------------------------------

leanCandidate : Lean.LeanConsumerKernelBypassCandidate
leanCandidate = Lean.canonicalLeanConsumerKernelBypassCandidate

stressBoundary : Stress.MksolVContextStressBoundary
stressBoundary = Stress.canonicalMksolVContextStressBoundary

cadoFamilyBoundary : CADOFamily.CADOMksolContextFamilyBoundary
cadoFamilyBoundary = CADOFamily.canonicalCADOMksolContextFamilyBoundary

------------------------------------------------------------------------
-- Append-only provenance correction for the pinned mathlib import surface.
------------------------------------------------------------------------

record LeanPinnedImportCorrection : Set where
  constructor lean-pinned-import-correction
  field
    originalSourceCommit : String
    pinnedImportRegressionCommit : String
    pinnedImportFixCommit : String
    kernelModule : String
    latticeModule : String
    pinnedMathlibVersion : String
    sourceUsesPinnedExistingModules : Bool
    leanKernelReceiptObserved : Bool
open LeanPinnedImportCorrection public

currentLeanPinnedImportCorrection : LeanPinnedImportCorrection
currentLeanPinnedImportCorrection =
  lean-pinned-import-correction
    "eeebc3f16125c8af97de7058d180a8972d9e4805"
    "e0c402cd39cf73c5297e1df7d406fcda8a5a3715"
    "5fe94a413c1e5e3d559632a8b9ef0019360c0048"
    "Mathlib.Algebra.Module.Submodule.Ker"
    "Mathlib.Algebra.Module.Submodule.Lattice"
    "v4.28.0"
    true
    false

------------------------------------------------------------------------
-- Binding/payment boundary.
------------------------------------------------------------------------

record LeanJointKernelFamilyBindingBoundary : Set where
  constructor lean-joint-kernel-family-binding-boundary
  field
    leanJointKernelSourceWritten : Bool
    leanPinnedImportCorrectionWritten : Bool
    leanJointKernelKernelReceiptObserved : Bool

    syntheticTwoVFamilyReceiptObserved : Bool
    syntheticTwoVIntersectionKernelZeroObserved : Bool
    syntheticTwoVResultIsUniversal : Bool

    commonGeneratorModuleBindingPaid : Bool
    commonActionOutputModuleBindingPaid : Bool
    familyIndexBindingPaid : Bool
    everyDeclaredActionLinearMapBindingPaid : Bool
    formalJointKernelEqualityBindingPaid : Bool

    syntheticTwoVFamilyEligibleForLeanJointInjectivity : Bool
    genericLeanTheoremReplacesRankFingerprintSearchAfterBinding : Bool
    rankFingerprintSearchRemainsDominated : Bool

    sourceNativeCADOContextFamilyInterfaceWritten : Bool
    sourceNativeCADOEvaluatorAlreadyProvedLinear : Bool
    productionCADOFamilyBindingPaid : Bool
    sameObjectProductionContextsPaid : Bool
open LeanJointKernelFamilyBindingBoundary public

canonicalLeanJointKernelFamilyBindingBoundary : LeanJointKernelFamilyBindingBoundary
canonicalLeanJointKernelFamilyBindingBoundary =
  lean-joint-kernel-family-binding-boundary
    true
    true
    false
    true
    true
    false
    false
    false
    false
    false
    false
    false
    true
    true
    true
    false
    false
    false
    false

------------------------------------------------------------------------
-- Residual order.
--
-- Certification and semantic binding are independent: a kernel-certified Lean
-- theorem still cannot consume the RSA runtime receipt until the action family
-- is represented as the required family of linear maps.
------------------------------------------------------------------------

data LeanJointKernelFamilyBindingResidual : Set where
  obtainLeanJointKernelKernelReceipt : LeanJointKernelFamilyBindingResidual
  bindGeneratorCoefficientCarrierAsCommonLeanModule : LeanJointKernelFamilyBindingResidual
  bindActionOutputsAsCommonLeanModule : LeanJointKernelFamilyBindingResidual
  bindSyntheticTwoVContextsToLeanFamilyIndex : LeanJointKernelFamilyBindingResidual
  proveEachSyntheticActionConsumerLinear : LeanJointKernelFamilyBindingResidual
  bindZeroIntersectionReceiptToFormalJointKernelEquality : LeanJointKernelFamilyBindingResidual
  instantiateLeanJointInjectivityForSyntheticTwoVFamily : LeanJointKernelFamilyBindingResidual
  extendLinearityBindingToSourceNativeCADOContextFamily : LeanJointKernelFamilyBindingResidual
  bindSameObjectProductionContexts : LeanJointKernelFamilyBindingResidual

firstLeanJointKernelFamilyBindingResidual : LeanJointKernelFamilyBindingResidual
firstLeanJointKernelFamilyBindingResidual = obtainLeanJointKernelKernelReceipt
