module DASHI.Moonshine.Monster3BLinearEigenspaceRestrictionLeanReceiptExact where

------------------------------------------------------------------------
-- CROSS-PROVER SOURCE RECEIPT: LINEAR CENTRAL-EIGENSPACE COMPILER
--
-- Companion Lean #47 source-writes the generic statement that one actual
-- linear central operator on one actual linear group representation, together
-- with a chosen scalar eigenvalue and commutation with the action, defines the
-- literal eigen-equation as a linear subspace.  The commuting action preserves
-- that same subspace, and the restricted representation/inclusion intertwiner
-- are then compiler outputs.
--
-- This mirrors the shape of Agda's already-owned set-level
-- `inertiaActsWithinPhase`; it does not import Lean theorem authority and does
-- not manufacture the actual Monster central operator, zeta orientation or
-- same-object attachment to the historical selected sector.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

repository : String
repository = "chboishabba/dashi_lean4"

pullRequest : String
pullRequest = "47"

sourcePath : String
sourcePath = "Synthesis/MonsterLinearEigenspaceRestriction.lean"

regressionPath : String
regressionPath = "Synthesis/MonsterLinearEigenspaceRestrictionRegression.lean"

data SourceReceiptCreatesMonsterCentralOperator : Set where
data SetPhaseLawCreatesLinearEigenspace : Set where

sourceReceiptDoesNotCreateMonsterCentralOperator :
  SourceReceiptCreatesMonsterCentralOperator → ⊥
sourceReceiptDoesNotCreateMonsterCentralOperator ()

setPhaseLawDoesNotCreateLinearEigenspace :
  SetPhaseLawCreatesLinearEigenspace → ⊥
setPhaseLawDoesNotCreateLinearEigenspace ()

record Boundary : Set where
  constructor boundary
  field
    literalLinearEigenspaceCompilerSourceWritten : Bool
    commutingActionPreservesEigenspaceSourceWritten : Bool
    eigenspaceRestrictedRepresentationSourceWritten : Bool
    eigenspaceInclusionIntertwinerSourceWritten : Bool
    restrictionLinearityCompilerOutput : Bool
    agdaSetLevelInertiaPreservationAlreadyOwned : Bool
    sourcePresenceCreatesAgdaKernelProof : Bool
    actualMonsterCentralLinearOperatorPaidByReceipt : Bool
    actualZetaOrientationPaidByReceipt : Bool
    historicalSectorSameObjectAttachmentPaidByReceipt : Bool
open Boundary public

canonicalBoundary : Boundary
canonicalBoundary = boundary
  true true true true true true
  false false false false
