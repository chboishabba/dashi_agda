module DASHI.Moonshine.Monster3BSchurFromSimpleFDRepLeanReceiptExact where

------------------------------------------------------------------------
-- CROSS-PROVER SOURCE RECEIPT: SCHUR FROM SIMPLE FDREP
--
-- Mathlib already proves, over an algebraically closed field, that a simple
-- finite-dimensional finite-group representation has rank-one equivariant
-- endomorphism space (`FDRep.simple_iff_end_is_rank_one`) and that every
-- self-intertwiner of an irreducible finite-dimensional representation is
-- scalar (`Representation.IsIrreducible.
-- algebraMap_intertwiningMap_bijective_of_isAlgClosed`).
--
-- Companion Lean #47 now records these as the generic producer for the Schur
-- premise used by the multiplicity-coordinate compiler.  Therefore an extra
-- Monster-specific Schur certificate is not a genuine scientific input once
-- the SAME actual H_zeta is attached as the same simple complex FDRep.
--
-- This receipt does not import Lean theorem authority into Agda and does not
-- perform the actual Monster/Schrodinger -> FDRep same-object attachment.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

repository : String
repository = "chboishabba/dashi_lean4"

pullRequest : String
pullRequest = "47"

sourcePath : String
sourcePath = "Synthesis/MonsterSchurFromSimpleFDRep.lean"

mathlibSimpleEndTheorem : String
mathlibSimpleEndTheorem = "FDRep.simple_iff_end_is_rank_one"

mathlibScalarIntertwinerTheorem : String
mathlibScalarIntertwinerTheorem = "Representation.IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed"

data SourceReceiptCreatesMonsterFDRepAttachment : Set where

sourceReceiptDoesNotCreateMonsterFDRepAttachment :
  SourceReceiptCreatesMonsterFDRepAttachment → ⊥
sourceReceiptDoesNotCreateMonsterFDRepAttachment ()

record Boundary : Set where
  constructor boundary
  field
    simpleFDRepEndRankOneSourceWritten : Bool
    irreducibleSelfIntertwinersScalarSourceWritten : Bool
    mathlibAttributionPreserved : Bool
    algebraicClosureRequiredForScalarSurjectivity : Bool
    schurRemainsMonsterSpecificInput : Bool
    leanKernelAuthorityImportedIntoAgda : Bool
    actualMonsterFDRepAttachmentPaidByReceipt : Bool
open Boundary public

canonicalBoundary : Boundary
canonicalBoundary = boundary
  true true true true
  false false false
