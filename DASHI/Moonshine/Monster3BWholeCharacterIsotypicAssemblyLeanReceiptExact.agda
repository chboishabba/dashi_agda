module DASHI.Moonshine.Monster3BWholeCharacterIsotypicAssemblyLeanReceiptExact where

------------------------------------------------------------------------
-- CROSS-PROVER RECEIPT: GENERIC SEMISIMPLE / ISOTYPIC ASSEMBLY
--
-- DASHI Lean source:
--   repository  chboishabba/dashi_lean4
--   branch      agent/monster3b-fdrep-groupalgebra-adapter
--   source      Synthesis/MonsterWholeCharacterIsotypicAssembly.lean
--   regression  Synthesis/MonsterWholeCharacterIsotypicAssemblyRegression.lean
--   source/root head cea92e489c20b670489bdbb372a178a61befecb3
--
-- The theorem `finiteCopiesOfOneSimpleType` consumes the proof-relevant
-- classifier
--
--   every simple R-submodule of M is linearly equivalent to S
--
-- together with semisimplicity and finite generation, and applies mathlib's
-- `IsIsotypicOfType.linearEquiv_fun` to produce
--
--   exists n, Nonempty (M ≃ₗ[R] (Fin n -> S)).
--
-- Attribution boundary:
--   * mathlib v4.28.0 / Junyan Xu owns `IsIsotypicOfType` and
--     `IsIsotypicOfType.linearEquiv_fun`;
--   * DASHI owns only the small classifier-to-finite-copies adapter and its
--     Monster-facing composition/provenance boundary;
--   * this receipt records SOURCE PRESENCE, not a Lean kernel execution and not
--     an Agda proof of the Lean theorem.
--
-- Scientific boundary:
--   this generic assembly does not construct the actual Monster W_zeta|E
--   classifier, does not bind the literal Schrodinger module to the actual
--   constituent, does not prove that the copy count is 90 by dimension, and
--   does not choose a Fin90 basis.  Those remain same-object/source payments.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

repository : String
repository = "chboishabba/dashi_lean4"

branch : String
branch = "agent/monster3b-fdrep-groupalgebra-adapter"

sourcePath : String
sourcePath = "Synthesis/MonsterWholeCharacterIsotypicAssembly.lean"

regressionPath : String
regressionPath = "Synthesis/MonsterWholeCharacterIsotypicAssemblyRegression.lean"

sourceHead : String
sourceHead = "cea92e489c20b670489bdbb372a178a61befecb3"

mathlibVersion : String
mathlibVersion = "v4.28.0"

mathlibOwner : String
mathlibOwner = "Junyan Xu; mathlib contributors"

mathlibTheorem : String
mathlibTheorem = "IsIsotypicOfType.linearEquiv_fun"

data SourcePresenceCreatesKernelReceipt : Set where
data AssemblyCreatesMonsterClassifier : Set where
data AssemblyChoosesNinetyCopies : Set where
data NinetyCreatesFin90Basis : Set where

sourcePresenceDoesNotCreateKernelReceipt :
  SourcePresenceCreatesKernelReceipt → ⊥
sourcePresenceDoesNotCreateKernelReceipt ()

assemblyDoesNotCreateMonsterClassifier :
  AssemblyCreatesMonsterClassifier → ⊥
assemblyDoesNotCreateMonsterClassifier ()

assemblyDoesNotChooseNinetyCopies :
  AssemblyChoosesNinetyCopies → ⊥
assemblyDoesNotChooseNinetyCopies ()

ninetyDoesNotCreateFin90Basis : NinetyCreatesFin90Basis → ⊥
ninetyDoesNotCreateFin90Basis ()

record Boundary : Set where
  constructor boundary
  field
    pinnedMathlibIsotypicTheoremLocated : Bool
    classifierToIsotypicAssemblySourceWritten : Bool
    finiteCopyLinearEquivalenceSourceWritten : Bool
    regressionConsumerSourceWritten : Bool
    synthesisRootImportsAssembly : Bool
    leanKernelReceiptObserved : Bool
    agdaCrossProverProofImported : Bool
    actualMonsterSimpleTypeClassifierPaid : Bool
    actualCopyCountNinetyPaidByThisReceipt : Bool
    fin90BasisChosenByThisReceipt : Bool
open Boundary public

canonicalBoundary : Boundary
canonicalBoundary = boundary
  true true true true true
  false false false false false
