module DASHI.NumberTheory.Collatz.SyracuseParityCylinderLeanCrossProverWeldExact where

------------------------------------------------------------------------
-- LEAN / AGDA CROSS-PROVER RECEIPT FOR THE SYRACUSE CYLINDER INVERSE STEP
--
-- Pinned DASHI Lean source:
--   repository : chboishabba/dashi_lean4
--   branch     : collatz-syracuse-parity-cylinder-20261006
--   source file: AgdaMirror/CollatzSyracuseInv3Exact.lean
--
-- The Lean source proves, in Mathlib ZMod (2^m):
--   * coprime_three_two_pow
--   * three_mul_inv3
--   * inv3_mul_three
--   * oddBack_spec
--   * three_mul_injective
--   * oddBack_unique
--
-- This file records that source exactly.  It does NOT turn an external Lean
-- theorem into an Agda kernel proof, and it does not manufacture the full
-- parity-word <-> residue-cylinder induction.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

record LeanInv3SourceReceipt : Set where
  constructor lean-inv3-source-receipt
  field
    repository : String
    branch : String
    sourceFile : String
    coefficientCarrier : String
    modulusCarrier : String
    coprimeTheorem : String
    leftInverseTheorem : String
    rightInverseTheorem : String
    oddReverseSpecTheorem : String
    multiplicationInjectiveTheorem : String
    oddReverseUniqueTheorem : String

open LeanInv3SourceReceipt public

canonicalLeanInv3SourceReceipt : LeanInv3SourceReceipt
canonicalLeanInv3SourceReceipt =
  lean-inv3-source-receipt
    "chboishabba/dashi_lean4"
    "collatz-syracuse-parity-cylinder-20261006"
    "AgdaMirror/CollatzSyracuseInv3Exact.lean"
    "ZMod (2 ^ m)"
    "2 ^ m"
    "AgdaMirror.CollatzSyracuseInv3Exact.coprime_three_two_pow"
    "AgdaMirror.CollatzSyracuseInv3Exact.three_mul_inv3"
    "AgdaMirror.CollatzSyracuseInv3Exact.inv3_mul_three"
    "AgdaMirror.CollatzSyracuseInv3Exact.oddBack_spec"
    "AgdaMirror.CollatzSyracuseInv3Exact.three_mul_injective"
    "AgdaMirror.CollatzSyracuseInv3Exact.oddBack_unique"

------------------------------------------------------------------------
-- Wrong-type / promotion firewalls.
------------------------------------------------------------------------

data ExternalLeanInv3CreatesAgdaKernelProof : Set where
data OddReverseStepCreatesWholeCylinderIff : Set where
data FiniteCylinderIffCreatesCollatzStopping : Set where

externalLeanInv3DoesNotCreateAgdaKernelProof :
  ExternalLeanInv3CreatesAgdaKernelProof → ⊥
externalLeanInv3DoesNotCreateAgdaKernelProof ()

oddReverseStepDoesNotCreateWholeCylinderIff :
  OddReverseStepCreatesWholeCylinderIff → ⊥
oddReverseStepDoesNotCreateWholeCylinderIff ()

finiteCylinderIffDoesNotCreateCollatzStopping :
  FiniteCylinderIffCreatesCollatzStopping → ⊥
finiteCylinderIffDoesNotCreateCollatzStopping ()

record SyracuseParityCylinderLeanWeldBoundary : Set where
  constructor syracuse-parity-cylinder-lean-weld-boundary
  field
    externalLeanSourcePinned : Bool
    zmodTwoPowerCarrierObserved : Bool
    threeUnitSourceObserved : Bool
    oddReverseEquationObserved : Bool
    oddReverseUniquenessObserved : Bool
    agdaParityWordCarrierOwned : Bool
    agdaResidueCandidateOwned : Bool
    leanZModToAgdaNatModuloSameObjectPaid : Bool
    fullRecursiveCylinderInductionPaid : Bool
    externalLeanTheoremImportedIntoAgdaKernel : Bool
    universalIntegerStoppingPaid : Bool
    nextResidual : String

open SyracuseParityCylinderLeanWeldBoundary public

canonicalSyracuseParityCylinderLeanWeldBoundary :
  SyracuseParityCylinderLeanWeldBoundary
canonicalSyracuseParityCylinderLeanWeldBoundary =
  syracuse-parity-cylinder-lean-weld-boundary
    true true true true true
    true true
    false false false false
    "Pay the exact cross-prover carrier weld between Lean ZMod (2^m) and the Agda Nat-mod-2^m residue representation, then induct on BinaryWord using the already-proved Agda parity shift law.  Even branch uses x=2*S(x); odd branch uses the pinned Lean oddBack_spec/oddBack_unique theorem.  This closes the forward/reverse residue-cylinder iff but still does not imply any universal stopping theorem."

leanInv3SourcePinned :
  SyracuseParityCylinderLeanWeldBoundary.externalLeanSourcePinned
    canonicalSyracuseParityCylinderLeanWeldBoundary
  ≡ true
leanInv3SourcePinned = refl

fullCylinderInductionStillOpen :
  SyracuseParityCylinderLeanWeldBoundary.fullRecursiveCylinderInductionPaid
    canonicalSyracuseParityCylinderLeanWeldBoundary
  ≡ false
fullCylinderInductionStillOpen = refl
