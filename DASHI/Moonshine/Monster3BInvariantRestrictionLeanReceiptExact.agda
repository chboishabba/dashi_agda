module DASHI.Moonshine.Monster3BInvariantRestrictionLeanReceiptExact where

------------------------------------------------------------------------
-- CROSS-PROVER SOURCE RECEIPT: INVARIANT-SUBSPACE RESTRICTION COMPILER
--
-- Companion Lean #47 now source-writes the generic theorem that one actual
-- invariant linear subspace of one actual linear group action canonically
-- inherits a restricted linear representation and an equivariant inclusion.
-- Nested invariant subspaces are handled by a second application.
--
-- Consequently the Monster 3B consumer should not keep zero/add/scalar
-- preservation for the 196883 constituent or literal zeta sector as independent
-- source payments once those sectors are supplied as actual invariant linear
-- subspaces on the SAME ambient action.
--
-- This is a source-status receipt only.  It does not import Lean kernel theorem
-- authority into Agda and does not construct the actual Monster subspaces.
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
sourcePath = "Synthesis/MonsterInvariantRestriction.lean"

regressionPath : String
regressionPath = "Synthesis/MonsterInvariantRestrictionRegression.lean"

data SourceReceiptCreatesInvariantMonsterSubspace : Set where
data RestrictionCompilerCreatesSameObjectAttachment : Set where

sourceReceiptDoesNotCreateInvariantMonsterSubspace :
  SourceReceiptCreatesInvariantMonsterSubspace → ⊥
sourceReceiptDoesNotCreateInvariantMonsterSubspace ()

restrictionCompilerDoesNotCreateSameObjectAttachment :
  RestrictionCompilerCreatesSameObjectAttachment → ⊥
restrictionCompilerDoesNotCreateSameObjectAttachment ()

record Boundary : Set where
  constructor boundary
  field
    invariantSubspaceInterfaceSourceWritten : Bool
    restrictedRepresentationCompilerSourceWritten : Bool
    inclusionIntertwinerCompilerSourceWritten : Bool
    nestedRestrictionCompilerSourceWritten : Bool
    restrictionLinearityCompilerOutput : Bool
    sourcePresenceCreatesAgdaKernelProof : Bool
    actualMonsterInvariantSubspacePaidByReceipt : Bool
    actualZetaInvariantSubspacePaidByReceipt : Bool
open Boundary public

canonicalBoundary : Boundary
canonicalBoundary = boundary
  true true true true true
  false false false
