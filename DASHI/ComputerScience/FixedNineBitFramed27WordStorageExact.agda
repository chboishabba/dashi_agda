module DASHI.ComputerScience.FixedNineBitFramed27WordStorageExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)

import DASHI.ComputerScience.BinaryThreeBitTwoTritAntipodalCodecExact as Block
import DASHI.ComputerScience.BinaryThreeBitTrit27FibreLiftExact as Lift27
import DASHI.Foundations.BalancedTernaryAntipodalOrbitExact as Orbit

------------------------------------------------------------------------
-- GENERIC FIXED NINE-BIT / THREE-FRAMED-27 WORD REPRESENTATION
--
-- This owner is representation-only.  It makes no claim that arbitrary Nat
-- round-trips through nine bits; clients must prove their values lie inside the
-- bounded fixture they use.  BinaryWord9 itself does round-trip exactly through
-- the three framed 27-state cells.
------------------------------------------------------------------------

half : Nat → Nat
half 0 = 0
half 1 = 0
half (suc (suc n)) = suc (half n)

leastBit : Nat → Bool
leastBit 0 = false
leastBit 1 = true
leastBit (suc (suc n)) = leastBit n

record BinaryWord9 : Set where
  constructor binaryWord9
  field
    b0 b1 b2 b3 b4 b5 b6 b7 b8 : Bool

open BinaryWord9 public

encodeWord9 : Nat → BinaryWord9
encodeWord9 n =
  binaryWord9
    (leastBit n)
    (leastBit (half n))
    (leastBit (half (half n)))
    (leastBit (half (half (half n))))
    (leastBit (half (half (half (half n)))))
    (leastBit (half (half (half (half (half n))))))
    (leastBit (half (half (half (half (half (half n)))))))
    (leastBit (half (half (half (half (half (half (half n))))))))
    (leastBit (half (half (half (half (half (half (half (half n)))))))))

bitNat : Bool → Nat
bitNat false = 0
bitNat true = 1

double : Nat → Nat
double n = n + n

decodeWord9 : BinaryWord9 → Nat
decodeWord9 (binaryWord9 b0 b1 b2 b3 b4 b5 b6 b7 b8) =
  bitNat b0 + double
  (bitNat b1 + double
  (bitNat b2 + double
  (bitNat b3 + double
  (bitNat b4 + double
  (bitNat b5 + double
  (bitNat b6 + double
  (bitNat b7 + double
   (bitNat b8))))))))

block0 : BinaryWord9 → Block.Bit3
block0 word = Block.bits3 (b0 word) (b1 word) (b2 word)

block1 : BinaryWord9 → Block.Bit3
block1 word = Block.bits3 (b3 word) (b4 word) (b5 word)

block2 : BinaryWord9 → Block.Bit3
block2 word = Block.bits3 (b6 word) (b7 word) (b8 word)

record Ternary27Word3 : Set where
  constructor ternary27Word3
  field
    cell0 cell1 cell2 : Orbit.TritTriple

open Ternary27Word3 public

binaryWord9ToTernary27 : BinaryWord9 → Ternary27Word3
binaryWord9ToTernary27 word =
  ternary27Word3
    (Lift27.encodeBit3To27 (block0 word))
    (Lift27.encodeBit3To27 (block1 word))
    (Lift27.encodeBit3To27 (block2 word))

ternary27ToBinaryWord9 : Ternary27Word3 → BinaryWord9
ternary27ToBinaryWord9 (ternary27Word3 c0 c1 c2)
  with Block.decode2to3 (Lift27.projectPayload c0)
     | Block.decode2to3 (Lift27.projectPayload c1)
     | Block.decode2to3 (Lift27.projectPayload c2)
... | Block.bits3 a0 a1 a2 | Block.bits3 b0 b1 b2 | Block.bits3 c0 c1 c2 =
  binaryWord9 a0 a1 a2 b0 b1 b2 c0 c1 c2

binaryWordToTernaryRoundTrip :
  (word : BinaryWord9) →
  ternary27ToBinaryWord9 (binaryWord9ToTernary27 word) ≡ word
binaryWordToTernaryRoundTrip
  (binaryWord9 a0 a1 a2 b0 b1 b2 c0 c1 c2)
  rewrite Block.blockRoundTrip (Block.bits3 a0 a1 a2)
        | Block.blockRoundTrip (Block.bits3 b0 b1 b2)
        | Block.blockRoundTrip (Block.bits3 c0 c1 c2) = refl

mapList : ∀ {A B : Set} → (A → B) → List A → List B
mapList f [] = []
mapList f (x ∷ xs) = f x ∷ mapList f xs

encodeBinaryMemory : List Nat → List BinaryWord9
encodeBinaryMemory = mapList encodeWord9

decodeBinaryMemory : List BinaryWord9 → List Nat
decodeBinaryMemory = mapList decodeWord9

encodeTernary27Memory : List Nat → List Ternary27Word3
encodeTernary27Memory words =
  mapList binaryWord9ToTernary27 (encodeBinaryMemory words)

decodeTernary27Memory : List Ternary27Word3 → List Nat
decodeTernary27Memory words =
  mapList decodeWord9 (mapList ternary27ToBinaryWord9 words)

binaryCellsPerWord : Nat
binaryCellsPerWord = 9

ternary27CellsPerWord : Nat
ternary27CellsPerWord = 3

record FixedNineBitFramed27Boundary : Set where
  constructor fixedNineBitFramed27Boundary
  field
    binaryWordRoundTripsThroughTernary27 : Bool
    threeBinaryBlocksPerWord : Bool
    threeFramed27CellsPerWord : Bool
    genericArbitraryNatRoundTripClaimed : Bool
    physicalCostClaimed : Bool

canonicalFixedNineBitFramed27Boundary : FixedNineBitFramed27Boundary
canonicalFixedNineBitFramed27Boundary =
  fixedNineBitFramed27Boundary true true true false false
