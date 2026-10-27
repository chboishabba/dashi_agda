module DASHI.Analysis.CollatzSyracuseAlignedBlockDescentExact where

------------------------------------------------------------------------
-- LITERAL ALIGNED-BLOCK DESCENT TRANSPORT
--
-- The aligned block is already in exact bijection with BinaryWord m.  For the
-- five-eighths horizons m = 8n+1, every start satisfying x >= 3^m whose parity
-- word is Good descends after m literal Syracuse steps.  Therefore any
-- non-descending start in such a block must map to the exact bad-word carrier.
--
-- The lower-bound hypothesis is kept explicit because the residue-ordered block
-- is cyclic: residue zero represents the top endpoint of the literal block.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)
open import Data.Fin.Base using (Fin)
open import Data.Nat using (_≤_; _<_)
open import Relation.Nullary.Negation.Core using (¬_; contradiction)

import DASHI.Core.BinaryBranchOutcomeEnumerationExact as Binary
import DASHI.NumberTheory.Collatz.SyracuseExact as Syracuse
import DASHI.NumberTheory.Collatz.SyracuseParityCylinderExact as Cylinder
import DASHI.NumberTheory.Collatz.SyracuseAffineIterateExact as Affine
import DASHI.Analysis.CollatzSyracuseAlignedBlockUniformityExact as Aligned
import DASHI.Analysis.CollatzSyracuseParityDescentEventExact as Event

horizon : Nat → Nat
horizon n = 8 * n + 1

alignedStart :
  (n block : Nat) →
  Fin (Cylinder.pow2 (horizon n)) →
  Syracuse.PositiveNat
alignedStart n block = Aligned.alignedBlockStart block

alignedWord :
  (n block : Nat) →
  Fin (Cylinder.pow2 (horizon n)) →
  Binary.BinaryWord (horizon n)
alignedWord n block = Aligned.alignedBlockWord block

largeAlignedStartGoodImpliesDescent :
  (n block : Nat) →
  (index : Fin (Cylinder.pow2 (horizon n))) →
  Affine.powNat 3 (horizon n)
    ≤ Syracuse.toNat (alignedStart n block index) →
  Event.parityDriftGood (alignedWord n block index) →
  Syracuse.toNat
      (Syracuse.syracuseIterate (horizon n) (alignedStart n block index))
    < Syracuse.toNat (alignedStart n block index)
largeAlignedStartGoodImpliesDescent n block index startLarge good =
  Event.goodParityWordImpliesDescent
    (horizon n)
    (alignedStart n block index)
    startLarge
    good

nonDescentImpliesBadWord :
  (n block : Nat) →
  (index : Fin (Cylinder.pow2 (horizon n))) →
  Affine.powNat 3 (horizon n)
    ≤ Syracuse.toNat (alignedStart n block index) →
  ¬ (Syracuse.toNat
      (Syracuse.syracuseIterate (horizon n) (alignedStart n block index))
      < Syracuse.toNat (alignedStart n block index)) →
  Event.parityDriftGoodᵇ (alignedWord n block index) ≡ false
nonDescentImpliesBadWord n block index startLarge nonDescent
  with Event.parityDriftGoodᵇ (alignedWord n block index) in decision
... | false = refl
... | true =
  let
    good = Event.parityDriftGoodᵇTrue (alignedWord n block index) decision
    descent = largeAlignedStartGoodImpliesDescent n block index startLarge good
  in
  contradiction descent nonDescent

record AlignedBlockDescentBoundary : Set where
  constructor alignedBlockDescentBoundary
  field
    alignedWordBijectionOwned : Nat
    goodWordToLiteralDescentOwned : Nat
    nonDescentToBadWordOwned : Nat
    largeStartHypothesisExplicit : Nat
    universalStoppingOwned : Nat

canonicalAlignedBlockDescentBoundary : AlignedBlockDescentBoundary
canonicalAlignedBlockDescentBoundary =
  alignedBlockDescentBoundary 1 1 1 1 0
