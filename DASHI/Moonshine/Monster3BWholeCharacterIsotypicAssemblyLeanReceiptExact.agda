module DASHI.Moonshine.Monster3BWholeCharacterIsotypicAssemblyLeanReceiptExact where

------------------------------------------------------------------------
-- CROSS-PROVER RECEIPT: GENERIC SEMISIMPLE / ISOTYPIC ASSEMBLY
--
-- Companion Lean source writes the generic theorem
--
--   every simple R-submodule of M is linearly equivalent to S
--     -> exists n, Nonempty (M ~= (Fin n -> S))
--
-- through mathlib `IsIsotypicOfType.linearEquiv_fun`.
--
-- The separate copy-count theorem is deliberately post-recognition: only after
-- an actual same-object finite-copy equivalence is paid may
-- 65610 = 90 * 729 determine n=90.  The arithmetic cannot create isotypy.
--
-- This Agda owner records source presence and the attribution/promotion
-- boundary; it does not claim a Lean kernel receipt or import the Lean theorem.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

repository : String
repository = "chboishabba/dashi_lean4"

pullRequest : String
pullRequest = "47"

branch : String
branch = "agent/e6-f3-exterior-square-maxcut-20261006"

sourcePath : String
sourcePath = "Synthesis/MonsterWholeCharacterIsotypicAssembly.lean"

regressionPath : String
regressionPath = "Synthesis/MonsterWholeCharacterIsotypicAssemblyRegression.lean"

sourceHead : String
sourceHead = "b0f8b1893fe5930060b76567db03220856c52063"

mathlibVersion : String
mathlibVersion = "v4.28.0"

mathlibOwner : String
mathlibOwner = "Junyan Xu; mathlib contributors"

mathlibTheorem : String
mathlibTheorem = "IsIsotypicOfType.linearEquiv_fun"

data SourcePresenceCreatesKernelReceipt : Set where
data AssemblyCreatesMonsterClassifier : Set where
data BareDimensionCreatesRepresentationIdentity : Set where
data NinetyCreatesFin90Basis : Set where

sourcePresenceDoesNotCreateKernelReceipt :
  SourcePresenceCreatesKernelReceipt → ⊥
sourcePresenceDoesNotCreateKernelReceipt ()

assemblyDoesNotCreateMonsterClassifier :
  AssemblyCreatesMonsterClassifier → ⊥
assemblyDoesNotCreateMonsterClassifier ()

bareDimensionDoesNotCreateRepresentationIdentity :
  BareDimensionCreatesRepresentationIdentity → ⊥
bareDimensionDoesNotCreateRepresentationIdentity ()

ninetyDoesNotCreateFin90Basis : NinetyCreatesFin90Basis → ⊥
ninetyDoesNotCreateFin90Basis ()

record Boundary : Set where
  constructor boundary
  field
    pinnedMathlibIsotypicTheoremLocated : Bool
    classifierToIsotypicAssemblySourceWritten : Bool
    finiteCopyLinearEquivalenceSourceWritten : Bool
    postRecognitionCopyCountCompilerSourceWritten : Bool
    regressionConsumerSourceWritten : Bool
    sourcePresentOnCompanionPR47 : Bool
    leanKernelReceiptObserved : Bool
    agdaCrossProverProofImported : Bool
    actualMonsterSimpleTypeClassifierPaid : Bool
    actualCopyCountNinetyPaidByThisReceipt : Bool
    fin90BasisChosenByThisReceipt : Bool
open Boundary public

canonicalBoundary : Boundary
canonicalBoundary = boundary
  true true true true true true
  false false false false false
