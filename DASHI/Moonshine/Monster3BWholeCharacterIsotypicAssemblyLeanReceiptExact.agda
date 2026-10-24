module DASHI.Moonshine.Monster3BWholeCharacterIsotypicAssemblyLeanReceiptExact where

------------------------------------------------------------------------
-- CROSS-PROVER RECEIPT: GENERIC SEMISIMPLE / ISOTYPIC ASSEMBLY
--
-- DASHI Lean source is present on both the exploratory adapter branch and the
-- live companion max-cut PR #47.  The live PR head pinned here is:
--
--   repository  chboishabba/dashi_lean4
--   PR          #47
--   branch      agent/e6-f3-exterior-square-maxcut-20261006
--   source      Synthesis/MonsterWholeCharacterIsotypicAssembly.lean
--   regression  Synthesis/MonsterWholeCharacterIsotypicAssemblyRegression.lean
--   head        b0f8b1893fe5930060b76567db03220856c52063
--
-- `finiteCopiesOfOneSimpleType` consumes the proof-relevant classifier
--
--   every simple R-submodule of M is linearly equivalent to S
--
-- together with semisimplicity and finite generation, and applies mathlib's
-- `IsIsotypicOfType.linearEquiv_fun` to produce
--
--   exists n, Nonempty (M ≃ₗ[R] (Fin n -> S)).
--
-- `finiteCopyCountOfFinrankRatio` is a deliberately POST-RECOGNITION theorem:
-- after an actual same-object equivalence M ~= (Fin n -> S) is paid and S has
-- positive finrank, the actual finrank equation may cancel finrank(S) and pin
-- n.  Thus the Monster equality 65610 = 90*729 may lawfully determine 90 only
-- AFTER isotypic same-object recognition; it cannot manufacture that
-- recognition beforehand.
--
-- Attribution boundary:
--   * mathlib v4.28.0 / Junyan Xu owns `IsIsotypicOfType` and
--     `IsIsotypicOfType.linearEquiv_fun`;
--   * mathlib contributors own the generic finite-product finrank API;
--   * DASHI owns only the small adapters/composition and the provenance
--     firewall around when numeric cancellation is admissible;
--   * this receipt records SOURCE PRESENCE, not a Lean kernel execution and not
--     an Agda proof of the Lean theorem.
--
-- Scientific boundary:
--   this generic assembly does not construct the actual Monster W_zeta|E
--   classifier and does not bind the literal Schrodinger module to the actual
--   restricted sector.  The post-recognition theorem can select copy count 90
--   only after that semantic payment.  It still does not choose a Fin90 basis.
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
