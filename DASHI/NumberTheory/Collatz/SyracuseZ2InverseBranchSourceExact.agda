module DASHI.NumberTheory.Collatz.SyracuseZ2InverseBranchSourceExact where

------------------------------------------------------------------------
-- PINNED 2-ADIC INVERSE-BRANCH SOURCE
--
-- Upstream source:
--   repository : sneed-and-feed/adelic-spectral-zeta
--   revision   : 0c3e98c144796f99534f372b4aba977e6b76ee19
--   file       : formalization/Formalization/Dynamics/CollatzZ2.lean
--
-- That file defines on the 2-adic integers:
--
--   inv0 x = 2*x
--   inv1 x = (2*x - 1) * inv(3)
--
-- proves inv0 is even and inv1 is odd, and defines a transfer operator by
-- averaging pullback along exactly these two branches.
--
-- This is the correct algebraic donor for the Syracuse parity-cylinder inverse
-- step.  It is deliberately kept separate from ContinuousTransfer.lean and
-- CollatzRelMatrix.lean, whose branches are 3x and 3x-1.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

record SyracuseZ2InverseBranchSource : Set where
  constructor syracuse-z2-inverse-branch-source
  field
    repository : String
    revision : String
    sourceFile : String
    carrier : String
    inverseZeroDefinition : String
    inverseOneDefinition : String
    inverseZeroParityTheorem : String
    inverseOneParityTheorem : String
    transferOperatorDefinition : String

open SyracuseZ2InverseBranchSource public

canonicalSyracuseZ2InverseBranchSource : SyracuseZ2InverseBranchSource
canonicalSyracuseZ2InverseBranchSource =
  syracuse-z2-inverse-branch-source
    "sneed-and-feed/adelic-spectral-zeta"
    "0c3e98c144796f99534f372b4aba977e6b76ee19"
    "formalization/Formalization/Dynamics/CollatzZ2.lean"
    "PadicInt / Z_2"
    "CollatzZ2.inv0 x = 2 * x"
    "CollatzZ2.inv1 x = (2 * x - 1) * PadicInt.inv 3"
    "CollatzZ2.inv0_is_even"
    "CollatzZ2.inv1_is_odd"
    "CollatzZ2.collatzTransferOp"

------------------------------------------------------------------------
-- Promotion firewalls.
------------------------------------------------------------------------

data Z2InverseFormulaCreatesFiniteNatCylinderProof : Set where
data Z2TransferDefinitionCreatesIntegerStoppingTheorem : Set where
data RelationMatrixSpectrumTransfersToZ2InverseOperator : Set where

z2FormulaDoesNotCreateFiniteNatCylinderProof :
  Z2InverseFormulaCreatesFiniteNatCylinderProof → ⊥
z2FormulaDoesNotCreateFiniteNatCylinderProof ()

z2TransferDoesNotCreateIntegerStoppingTheorem :
  Z2TransferDefinitionCreatesIntegerStoppingTheorem → ⊥
z2TransferDoesNotCreateIntegerStoppingTheorem ()

relationSpectrumDoesNotTransferAutomatically :
  RelationMatrixSpectrumTransfersToZ2InverseOperator → ⊥
relationSpectrumDoesNotTransferAutomatically ()

record SyracuseZ2InverseBranchBoundary : Set where
  constructor syracuse-z2-inverse-branch-boundary
  field
    correctInverseBranchFormulaObserved : Bool
    inverseBranchParityObserved : Bool
    inverseBranchTransferOperatorObserved : Bool
    finiteNatModuloSameObjectWeldPaid : Bool
    relationMatrixSpectrumReusableWithoutProof : Bool
    universalStoppingPaid : Bool

open SyracuseZ2InverseBranchBoundary public

canonicalSyracuseZ2InverseBranchBoundary : SyracuseZ2InverseBranchBoundary
canonicalSyracuseZ2InverseBranchBoundary =
  syracuse-z2-inverse-branch-boundary true true true false false false

correctZ2BranchDonorFound :
  correctInverseBranchFormulaObserved canonicalSyracuseZ2InverseBranchBoundary
  ≡ true
correctZ2BranchDonorFound = refl

relationSpectrumStillNotReusable :
  relationMatrixSpectrumReusableWithoutProof canonicalSyracuseZ2InverseBranchBoundary
  ≡ false
relationSpectrumStillNotReusable = refl
