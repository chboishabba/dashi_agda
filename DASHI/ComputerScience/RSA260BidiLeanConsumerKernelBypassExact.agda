module DASHI.ComputerScience.RSA260BidiLeanConsumerKernelBypassExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- CROSS-PROVER LEAN BYPASS CANDIDATE
--
-- The Lean source is deliberately domain-neutral.  It states that for a
-- family of linear consumers A_i, equality of every output is equivalent to
-- the state difference lying in the intersection of the kernels, and that a
-- trivial joint kernel makes the family jointly injective.
--
-- This owner records source/provenance/status only.  It does NOT import Lean
-- proof authority into Agda, bind the theorem to CADO mksol semantics, create
-- same-object RSA-260 artifacts, or certify the Lean source.
------------------------------------------------------------------------

record LeanConsumerKernelBypassCandidate : Set where
  constructor lean-consumer-kernel-bypass-candidate
  field
    repository : String
    toolchain : String
    mathlibVersion : String
    branch : String
    redCommit : String
    sourceCommit : String
    sourcePath : String
    regressionPath : String
    equivalenceTheorem : String
    injectivityTheorem : String

    leanSourceWritten : Bool
    leanKernelReceiptObserved : Bool
    crossProverTransportObserved : Bool
    rsaProductionBindingObserved : Bool
open LeanConsumerKernelBypassCandidate public

canonicalLeanConsumerKernelBypassCandidate : LeanConsumerKernelBypassCandidate
canonicalLeanConsumerKernelBypassCandidate =
  lean-consumer-kernel-bypass-candidate
    "chboishabba/dashi_lean4"
    "leanprover/lean4:v4.28.0"
    "mathlib v4.28.0"
    "agent/rsa-consumer-kernel-bypass"
    "96854397e3547e08fd59c2c9a25f5c18a441a68a"
    "eeebc3f16125c8af97de7058d180a8972d9e4805"
    "Synthesis/LinearConsumerKernelQuotient.lean"
    "Synthesis/LinearConsumerKernelQuotientRegression.lean"
    "Synthesis.same_outputs_iff_sub_mem_iInf_ker"
    "Synthesis.jointly_injective_of_iInf_ker_eq_bot"
    true false false false

------------------------------------------------------------------------
-- WrongType / authority firewalls.
------------------------------------------------------------------------

data LeanSourceCreatesKernelReceipt : Set where
data GenericKernelTheoremCreatesCADOBinding : Set where
data TrivialSyntheticKernelCreatesProductionInjectivity : Set where

leanSourceDoesNotCreateKernelReceipt : LeanSourceCreatesKernelReceipt -> ⊥
leanSourceDoesNotCreateKernelReceipt ()

genericKernelTheoremDoesNotCreateCADOBinding : GenericKernelTheoremCreatesCADOBinding -> ⊥
genericKernelTheoremDoesNotCreateCADOBinding ()

trivialSyntheticKernelDoesNotCreateProductionInjectivity :
  TrivialSyntheticKernelCreatesProductionInjectivity -> ⊥
trivialSyntheticKernelDoesNotCreateProductionInjectivity ()

record LeanConsumerKernelBypassBoundary : Set where
  constructor lean-consumer-kernel-bypass-boundary
  field
    genericJointKernelTheoremLocated : Bool
    genericJointKernelTheoremKernelCertified : Bool
    sameOutputsIffDifferenceInJointKernelSourceWritten : Bool
    trivialJointKernelImpliesJointInjectivitySourceWritten : Bool

    declaredConsumerFamilyBindingStillRequired : Bool
    trivialIntersectionKernelReceiptStillRequired : Bool
    theoremCanReplaceHandRecordedKernelLogicAfterCertification : Bool

    theoremCanReplaceRSASameObjectBinding : Bool
    theoremCreatesExactCADOMksolSemantics : Bool
    theoremCreatesProductionFactorCertificate : Bool

    nextResidual : String
open LeanConsumerKernelBypassBoundary public

canonicalLeanConsumerKernelBypassBoundary : LeanConsumerKernelBypassBoundary
canonicalLeanConsumerKernelBypassBoundary =
  lean-consumer-kernel-bypass-boundary
    true
    false
    true
    true
    true
    true
    true
    false
    false
    false
    "obtain a Lean kernel receipt for the generic consumer-family theorem, then bind the already-declared RSA synthetic/CADO action family to the theorem and supply the relevant joint-kernel receipt. The generic theorem never substitutes for same-object V, prepared-operator, range, or production-artifact identity."
