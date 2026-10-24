module DASHI.Moonshine.Monster3BTensorFiniteCopiesLeanReceiptExact where

------------------------------------------------------------------------
-- CROSS-PROVER SOURCE RECEIPT: TENSOR EVALUATION AFTER ISOTYPY
--
-- Companion Lean #47 consumes mathlib `TensorProduct.piScalarRight` to
-- source-write
--
--   H tensor (Fin n -> k) ~= (Fin n -> H),
--
-- and composes this with an already-paid finite-copy recognition of W to obtain
--
--   H tensor k^n ~= W.
--
-- Hence the abstract tensor finite-copy/evaluation equivalence is not a further
-- Monster-specific input after actual isotypy and multiplicity-coordinate
-- recognition.  The actual same-object isotypic equivalence remains open.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

repository : String
repository = "chboishabba/dashi_lean4"
branch : String
branch = "agent/e6-f3-exterior-square-maxcut-20261006"
sourcePath : String
sourcePath = "Synthesis/MonsterTensorEvaluationFiniteCopies.lean"
mathlibTheorem : String
mathlibTheorem = "TensorProduct.piScalarRight"

record Boundary : Set where
  constructor boundary
  field
    mathlibPiScalarRightConsumed : Bool
    tensorFiniteCopiesCompilerSourceWritten : Bool
    postIsotypyTensorEquivalenceSourceWritten : Bool
    ninetyTensorSpecializationSourceWritten : Bool
    tensorEquivalenceStillMonsterSpecificInput : Bool
    leanKernelAuthorityImportedIntoAgda : Bool
    actualMonsterIsotypicEquivalencePaidByReceipt : Bool
open Boundary public

canonicalBoundary : Boundary
canonicalBoundary = boundary
  true true true true false false false
