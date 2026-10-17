module DASHI.Analysis.CollatzSyracuseAlignedBlockUniformityExact where

------------------------------------------------------------------------
-- EVERY ALIGNED 2^m BLOCK HAS THE SAME EXACT PARITY-WORD BIJECTION
--
-- Starting from the canonical positive representative block {1,...,2^m}, add
-- k*2^m to every starting integer.  The level-m residue is unchanged, hence the
-- proved residue-cylinder classifier gives the same parity word exactly.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)
open import Data.Fin.Base using (Fin)
open import Data.Nat.DivMod using (_%_; [m+kn]%n≡m%n)
open import Relation.Binary.PropositionalEquality using (sym; trans)

import DASHI.Core.BinaryBranchOutcomeEnumerationExact as Binary
import DASHI.Core.FiniteUniformBijectionTransportExact as Uniform
import DASHI.NumberTheory.Collatz.SyracuseExact as Syracuse
import DASHI.NumberTheory.Collatz.SyracuseParityItineraryExact as Itinerary
import DASHI.NumberTheory.Collatz.SyracuseParityCylinderExact as Cylinder
import DASHI.NumberTheory.Collatz.SyracuseParityCylinderOddBranchExact as Odd
import DASHI.NumberTheory.Collatz.SyracusePow2ArithmeticExact as Pow2
import DASHI.Analysis.CollatzSyracuseCompleteBlockBijectionExact as Block

shiftPositiveBy : Nat → Syracuse.PositiveNat → Syracuse.PositiveNat
shiftPositiveBy shift (Syracuse.positiveNat predecessor) =
  Syracuse.positiveNat (predecessor + shift)

shiftPositiveByToNat :
  (shift : Nat) →
  (x : Syracuse.PositiveNat) →
  Syracuse.toNat (shiftPositiveBy shift x)
  ≡ Syracuse.toNat x + shift
shiftPositiveByToNat shift (Syracuse.positiveNat predecessor) = refl

alignedBlockStart :
  {m : Nat} →
  Nat →
  Fin (Cylinder.pow2 m) →
  Syracuse.PositiveNat
alignedBlockStart {m} block index =
  shiftPositiveBy (block * Cylinder.pow2 m) (Block.blockStart index)

alignedBlockResidue :
  {m : Nat} →
  (block : Nat) →
  (index : Fin (Cylinder.pow2 m)) →
  Syracuse.toNat (alignedBlockStart block index) % Cylinder.pow2 m
  ≡ Syracuse.toNat (Block.blockStart index) % Cylinder.pow2 m
alignedBlockResidue {m} block index =
  let
    instance modulus-nonzero = Pow2.pow2NonZero m
    base = Syracuse.toNat (Block.blockStart index)
    modulus = Cylinder.pow2 m
  in
  trans
    (cong (_% modulus) (shiftPositiveByToNat (block * modulus) (Block.blockStart index)))
    ([m+kn]%n≡m%n base block modulus)
  where
  open import Relation.Binary.PropositionalEquality using (cong)

alignedBlockWord :
  {m : Nat} →
  Nat →
  Fin (Cylinder.pow2 m) →
  Binary.BinaryWord m
alignedBlockWord {m} block index =
  Itinerary.parityWord m (alignedBlockStart block index)

alignedBlockWordEqualsCanonical :
  {m : Nat} →
  (block : Nat) →
  (index : Fin (Cylinder.pow2 m)) →
  alignedBlockWord block index ≡ Block.blockWord index
alignedBlockWordEqualsCanonical {m} block index =
  let
    word = Block.blockWord index

    canonicalResidue :
      Syracuse.toNat (Block.blockStart index) % Cylinder.pow2 m
      ≡ Cylinder.residueOfParityWord Odd.canonicalParityCylinderSource word
    canonicalResidue =
      Cylinder.parityWordImpliesResidue
        Odd.canonicalParityCylinderSource
        word
        (Block.blockStart index)
        refl

    shiftedResidue :
      Syracuse.toNat (alignedBlockStart block index) % Cylinder.pow2 m
      ≡ Cylinder.residueOfParityWord Odd.canonicalParityCylinderSource word
    shiftedResidue =
      trans (alignedBlockResidue block index) canonicalResidue
  in
  Cylinder.residueImpliesParityWord
    Odd.canonicalParityCylinderSource
    word
    (alignedBlockStart block index)
    shiftedResidue

alignedBlockBijection :
  {m : Nat} →
  (block : Nat) →
  Uniform.ExplicitBijection
    (Fin (Cylinder.pow2 m))
    (Binary.BinaryWord m)
alignedBlockBijection {m} block = record
  { Uniform.to = alignedBlockWord block
  ; Uniform.from = Block.inverseWordIndex
  ; Uniform.fromTo = λ index →
      trans
        (cong Block.inverseWordIndex (alignedBlockWordEqualsCanonical block index))
        (Block.indexRoundTrip index)
  ; Uniform.toFrom = λ word →
      trans
        (alignedBlockWordEqualsCanonical block (Block.inverseWordIndex word))
        (Block.inverseWordRoundTrip word)
  }
  where
  open import Relation.Binary.PropositionalEquality using (cong)

alignedBlockUniformWordMass :
  {m : Nat} →
  (block : Nat) →
  Uniform.UniformNatMass (Binary.BinaryWord m)
alignedBlockUniformWordMass block =
  Uniform.transportUnitMass (alignedBlockBijection block)

record AlignedBlockUniformityBoundary : Set where
  constructor alignedBlockUniformityBoundary
  field
    allAlignedBlocksOwned : Nat
    spectralMixingRequired : Nat
    arbitraryUnalignedIntervalFullyPaid : Nat
    boundaryFragmentsStillNeedCounting : Nat

canonicalAlignedBlockUniformityBoundary : AlignedBlockUniformityBoundary
canonicalAlignedBlockUniformityBoundary = alignedBlockUniformityBoundary 1 0 0 1
